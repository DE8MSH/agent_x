/*
  Priyom Events -> Top 10 bis Mitternacht (Berlin) + UDP + optional FRG-100 CAT
  - Tagesliste nur beim Boot (Retry nach 10 s bei Fehler)
  - Live-Events 3 min grün
  - Details: calendar-time/voice/frequency/mode/remarks in Arrays
  - UDP: kHz ASCII an 192.168.178.61:8080
         DEBUG==1 -> mit '\n', DEBUG==0 -> ohne
  - Mehrfach-QRG zur gleichen Uhrzeit:
      * Rotation in Listenreihenfolge (1., 2., 3., …)
      * alle 5 s umschalten, insgesamt 2 Minuten
      * bei jedem Wechsel QRG per UDP schicken
  - Einzel-QRG: genau 1× senden
  - Danach warten bis nächstes Live-Set beginnt
  - FRG-100: per Flag FRG100 (0=aus, 1=an). Keine Spam-Befehle.
  - ATS: UDP-Test 146/6070/11223 kHz (je 5 s) nach erstem Laden
*/

#include <WiFi.h>
#include <WiFiClientSecure.h>
#include <WiFiUdp.h>
#include <HTTPClient.h>
#include <ArduinoJson.h>   // v7.x
#include <TFT_eSPI.h>
#include <time.h>
#include <vector>
#include <algorithm>
#include <ctype.h>

// ---------- Debug ----------
#define DEBUG 1     // 1 -> UDP mit '\n', 0 -> ohne Newline
#if DEBUG
  #define DBG(...) Serial.printf(__VA_ARGS__)
#else
  #define DBG(...) do{}while(0)
#endif

// ---------- Schalter ----------
#define TESTTT 1
#define ATS    1
#define FRG100 0

// ---------- WLAN ----------
#include "cred.h" // WIFI_SSID, WIFI_PASSWORD

// ---------- API ----------
const char* BASE_URL = "https://calendar2.priyom.org/events";
const char* UA_EDGE =
  "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
  "AppleWebKit/537.36 (KHTML, like Gecko) "
  "Chrome/124.0.0.0 Safari/537.36 Edg/124.0.0.0";

// ---------- Zeit / TZ ----------
const char* TZ_EU_BERLIN = "CET-1CEST,M3.5.0/2,M10.5.0/3";

// ---------- Display ----------
TFT_eSPI tft = TFT_eSPI(); // 320x240

// ---------- Logos ----------
#include "priyom_logo_bw.h"
#include "agent3_logo.h"
#include "dlbb_logo.h"

// ---------- Sprites ----------
TFT_eSprite agent3Sprite = TFT_eSprite(&tft);
TFT_eSprite dlbbSprite   = TFT_eSprite(&tft);
TFT_eSprite hudSprite    = TFT_eSprite(&tft);

// ---------- HUD-Layout ----------
int HUD_W = 0, HUD_H = 0, HUD_X = 0, HUD_Y = 0;
int g_logoX = 0, g_logoY = 4;
int g_lineY = 0;

// ---------- Live-Fenster ----------
static const uint32_t LIVE_WINDOW_SEC = 180; // Anzeige-Fenster (grün)

// ---------- Datentyp ----------
struct EventItem { time_t startUtc; String summary; };

// ---------- State ----------
std::vector<EventItem> g_events;
String g_lastErr;
time_t g_nextEventUtc = 0; String g_nextSummary;

// ---------- Detail-Arrays ----------
std::vector<String> g_cal_time, g_cal_voice, g_cal_frequency, g_cal_mode, g_cal_remarks;

// ---------- Retry ----------
bool g_loadedOnce = false;
uint32_t g_nextRetryMs = 0;

// ---------- CAT (FRG-100) ----------
#define CAT_TX_PIN      27
#define CAT_BAUD        4800
#define CAT_SERIAL_CONF SERIAL_8N2
HardwareSerial& CAT = Serial2;

bool     g_catOn     = false;
uint32_t g_catFreqHz = 0;
uint8_t  g_catMode   = 255;

// ---------- UDP ----------
WiFiUDP g_udp;
IPAddress UDP_DST_IP(192,168,178,61);
const uint16_t UDP_DST_PORT = 8080;

// ---------- Rotation / Fenster ----------
String   g_liveSigPrev = "";
uint32_t g_windowStartMs = 0;   // Start des 2-Minuten-Rotationsfensters
bool     g_rotActive = false;   // true bei >=2 Live-Stationen
uint32_t g_rotNextSwitchMs = 0; // alle 5 s
size_t   g_rotCursor = 0;       // Index in live-Liste
// für Einzelstation: nur 1× senden
bool     g_singleSent = false;

// ---------- TZ Helper ----------
static inline void ensureTZBerlin(){ setenv("TZ", TZ_EU_BERLIN, 1); tzset(); }

// ---------- Helpers ----------
String urlEncode(const String& s){
  String out; const char* hex="0123456789ABCDEF";
  for (size_t i=0;i<s.length();i++){
    unsigned char c=(unsigned char)s[i];
    if (isalnum(c)||c=='-'||c=='_'||c=='.'||c=='~') out+=(char)c;
    else if (c==' ') out+='+';
    else { out+='%'; out+=hex[(c>>4)&0xF]; out+=hex[c&0xF]; }
  }
  return out;
}
String iso8601Z_ms(time_t tUtc){ struct tm tmp; gmtime_r(&tUtc,&tmp); char buf[40]; strftime(buf,sizeof(buf),"%Y-%m-%dT%H:%M:%S",&tmp); return String(buf)+".000Z"; }
time_t timegm_compat(struct tm* tmUtc){ char* oldtz=getenv("TZ"); if(oldtz) oldtz=strdup(oldtz); setenv("TZ","UTC0",1); tzset(); time_t t=mktime(tmUtc); if(oldtz){ setenv("TZ",oldtz,1); free(oldtz);} else unsetenv("TZ"); tzset(); return t; }
time_t midnightBerlinFor(time_t nowUtc){ ensureTZBerlin(); struct tm local; localtime_r(&nowUtc,&local); local.tm_mday+=1; local.tm_hour=0; local.tm_min=0; local.tm_sec=0; return mktime(&local); }
String fmtTimeLocalHHMM(time_t tUtc){ ensureTZBerlin(); struct tm loc; localtime_r(&tUtc,&loc); char buf[8]; strftime(buf,sizeof(buf),"%H:%M",&loc); return String(buf); }
String fmtTimeLocalFull(time_t tUtc){ ensureTZBerlin(); struct tm loc; localtime_r(&tUtc,&loc); char buf[24]; strftime(buf,sizeof(buf),"%Y-%m-%d %H:%M:%S",&loc); return String(buf); }

// --- Zahl-vor-Einheit extrahieren ---
static bool extractNumberBeforeUnit(const String& in, const char* unit, double& outVal){
  int u = in.indexOf(unit);
  if (u < 0) return false;
  int i = u - 1;
  while (i >= 0 && (isDigit((unsigned char)in[i]) || in[i]=='.' || in[i]==',' || in[i]==' ')) i--;
  int start = i + 1;
  while (start < u && in[start] == ' ') start++;
  if (start >= u) return false;
  String num = in.substring(start, u);
  num.replace(',', '.'); num.trim();
  if (num.length() == 0) return false;
  outVal = strtod(num.c_str(), nullptr);
  return (outVal > 0.0);
}
static bool hasUnit(const String& s){
  String t=s; t.toLowerCase();
  return t.indexOf("khz")>=0 || t.indexOf("mhz")>=0 || t.indexOf("hz")>=0;
}

// --- größtes Zahl-Token (für unitlose Werte) ---
static bool extractLargestNumberToken(const String& in, double& outVal){
  outVal = 0.0;
  bool found = false;
  const int N = in.length();
  int i = 0;
  while (i < N) {
    while (i < N && !(isDigit((unsigned char)in[i]) || in[i]=='.' || in[i]==',')) i++;
    if (i >= N) break;
    int start = i;
    while (i < N && (isDigit((unsigned char)in[i]) || in[i]=='.' || in[i]==',')) i++;
    int end = i;
    if (end > start) {
      String num = in.substring(start, end);
      num.replace(',', '.'); num.trim();
      if (num.length() && num != ".") {
        double v = strtod(num.c_str(), nullptr);
        if (v > 0.0) { if (!found || v > outVal) { outVal = v; found = true; } }
      }
    }
  }
  return found;
}

// --- Summary-Fallback: links von "kHz" 4..5 Ziffern nehmen ---
static bool extractKHz_4or5_leftOf_kHz_fromSummary(const String& summary, uint32_t& kHz){
  String s = summary; s.toLowerCase();
  int pos = s.indexOf("khz");
  if (pos < 0) return false;
  int i = pos - 1;
  while (i >= 0 && isspace((unsigned char)s[i])) i--;
  String digits = ""; int count = 0;
  while (i >= 0 && isDigit((unsigned char)s[i]) && count < 5) {
    digits = char(s[i]) + digits; i--; count++;
  }
  if (digits.length() < 4 || digits.length() > 5) return false;
  if (i >= 0 && isDigit((unsigned char)s[i])) return false;
  kHz = (uint32_t) strtoul(digits.c_str(), nullptr, 10);
  return (kHz > 0);
}

// --- Frequenz-Parser (robust; auch unitlos) ---
bool parseFrequencyHz(const String& raw, uint32_t& outHz){
  String s = raw; s.toLowerCase();
  s.replace("frequency", " "); s.replace("freq", " "); s.replace("f=", " ");
  s.replace("usb", " "); s.replace("lsb", " "); s.replace("am", " ");
  s.replace("fm", " ");  s.replace("cw", " "); s.replace("ssb", " ");
  s.replace("rtty", " "); s.replace("bps", " "); s.replace("baud", " ");
  s.replace(":", " "); s.replace("=", " "); s.trim();

  double val = 0.0; int unit = 0; // 3=MHz, 2=kHz, 1=Hz
  if (s.indexOf("mhz") >= 0 && extractNumberBeforeUnit(s, "mhz", val)) unit = 3;
  else if (s.indexOf("khz") >= 0 && extractNumberBeforeUnit(s, "khz", val)) unit = 2;
  else if (s.indexOf("hz")  >= 0 && extractNumberBeforeUnit(s, "hz",  val)) unit = 1;

  if (unit == 0) {
    if (!extractLargestNumberToken(s, val) || val <= 0.0) return false;
    if      (val <= 30.0)   unit = 3;
    else if (val <= 30000.) unit = 2;
    else                    unit = 1;
  }

  double hz = val;
  if      (unit == 3) hz *= 1e6;
  else if (unit == 2) hz *= 1e3;
  if (hz < 1e4 || hz > 3.0e8) return false;

  outHz = (uint32_t)((hz + 5.0) / 10.0) * 10u;
  return true;
}

// ---------- Layout & Header ----------
int listStartY(){ return g_lineY + 6; }
void drawHeaderAndHudFrame(){
  tft.fillScreen(TFT_BLACK);
  g_logoX=(tft.width()-priyom_logo_bw_WIDTH)/2; g_logoY=4;
  tft.pushImage(g_logoX,g_logoY,priyom_logo_bw_WIDTH,priyom_logo_bw_HEIGHT,priyom_logo_bw_data);
  HUD_W=tft.width()-8; HUD_H=16; HUD_X=4; HUD_Y=g_logoY+priyom_logo_bw_HEIGHT+2;
  g_lineY = HUD_Y + HUD_H + 2;
  tft.drawLine(0,g_lineY,tft.width()-1,g_lineY,TFT_DARKGREY);
}

// ---------- Events-Liste ----------
void drawEventsList(const std::vector<EventItem>& events, size_t maxShow=10){
  int y = listStartY() + 8; const int lineH=14;
  tft.setTextFont(1); tft.setTextSize(1);
  ensureTZBerlin(); time_t now=time(nullptr);
  size_t shown=0;
  for(const auto& e: events){
    if(now >= e.startUtc + LIVE_WINDOW_SEC) continue;
    bool live = (now >= e.startUtc) && (now < e.startUtc + LIVE_WINDOW_SEC);
    tft.setTextColor(live?TFT_GREEN:TFT_CYAN, TFT_BLACK);
    if(shown>=maxShow) break;
    String line = fmtTimeLocalHHMM(e.startUtc) + "  " + e.summary;
    if(line.length()>54) line = line.substring(0,53) + "…";
    tft.setCursor(8,y); tft.print(line); y+=lineH; shown++;
  }
  if(shown==0){
    tft.setCursor(8,y); tft.setTextColor(TFT_YELLOW,TFT_BLACK); tft.print("Keine anstehenden Sendungen heute.");
    y+=lineH; tft.setCursor(8,y); tft.setTextColor(TFT_DARKGREY,TFT_BLACK); if(g_lastErr.length()) tft.print(g_lastErr);
  }
}

// ---------- Frequenz-Ermittlung: frequency -> remarks/time (mit Einheit) -> summary (kHz-links-4..5) ----------
bool getFreqForIndex(size_t idx, uint32_t& outHz, String& rawOut){
  rawOut = "";
  // 1) calendar-frequency (darf unitlos sein)
  if (idx < g_cal_frequency.size() && g_cal_frequency[idx].length()){
    rawOut = g_cal_frequency[idx];
    if (parseFrequencyHz(rawOut, outHz)) return true;
  }
  // 2) remarks/time nur mit expliziter Einheit
  if (idx < g_cal_remarks.size() && g_cal_remarks[idx].length() && hasUnit(g_cal_remarks[idx])){
    rawOut = g_cal_remarks[idx];
    if (parseFrequencyHz(rawOut, outHz)) return true;
  }
  if (idx < g_cal_time.size() && g_cal_time[idx].length() && hasUnit(g_cal_time[idx])){
    rawOut = g_cal_time[idx];
    if (parseFrequencyHz(rawOut, outHz)) return true;
  }
  // 3) summary: links von "kHz" 4..5 Ziffern
  if (idx < g_events.size()){
    uint32_t kHz=0;
    if (extractKHz_4or5_leftOf_kHz_fromSummary(g_events[idx].summary, kHz)){
      outHz = kHz * 1000U;
      rawOut = String(kHz);
      return true;
    }
  }
  rawOut = "";
  return false;
}

// ---------- HUD ----------
void initHudSprite(){ hudSprite.setColorDepth(16); hudSprite.createSprite(HUD_W,HUD_H); hudSprite.setTextWrap(false); }
static inline void fmtHMS(uint32_t sec, char* out, size_t n){ uint32_t h=sec/3600; sec%=3600; uint32_t m=sec/60; sec%=60; snprintf(out,n,"%02u:%02u:%02u",(unsigned)h,(unsigned)m,(unsigned)sec); }
void updateClockHud(){
  if(!hudSprite.created()) return;
  ensureTZBerlin(); time_t now=time(nullptr);
  struct tm loc; if(!getLocalTime(&loc,5)){ localtime_r(&now,&loc); }
  char locStr[16]; strftime(locStr,sizeof(locStr),"%H:%M:%S",&loc);
  struct tm gm; gmtime_r(&now,&gm); char utcStr[16]; strftime(utcStr,sizeof(utcStr),"%H:%M:%S",&gm);
  char tminus[16]="--:--:--"; if(g_nextEventUtc>now){ uint32_t d=(uint32_t)(g_nextEventUtc-now); fmtHMS(d,tminus,sizeof(tminus)); }
  hudSprite.fillSprite(TFT_BLACK); hudSprite.setTextFont(1); hudSprite.setTextSize(1);
  const char* s1="LOC "; const char* s2="   UTC "; const char* s3="   T- ";
  int total_w=0; total_w += hudSprite.textWidth(s1)+hudSprite.textWidth(locStr);
  total_w += hudSprite.textWidth(s2)+hudSprite.textWidth(utcStr);
  total_w += hudSprite.textWidth(s3)+hudSprite.textWidth(tminus);
  int y=(HUD_H-8)/2; int x=(HUD_W-total_w)/2;
  auto seg=[&](const char* text, uint16_t fg){ hudSprite.setTextColor(fg,TFT_BLACK); hudSprite.setCursor(x,y); hudSprite.print(text); x+=hudSprite.textWidth(text); };
  seg(s1,TFT_WHITE); seg(locStr,TFT_CYAN); seg(s2,TFT_WHITE); seg(utcStr,TFT_CYAN); seg(s3,TFT_WHITE); seg(tminus,TFT_YELLOW);
  hudSprite.pushSprite(HUD_X,HUD_Y);
}

// ---------- Next-Cache + Debug ----------
void updateNextEventCache(const std::vector<EventItem>& events){
  ensureTZBerlin(); time_t now=time(nullptr);
  g_nextEventUtc=0; g_nextSummary=""; int nextIdx=-1;
  for(size_t i=0;i<events.size();++i){ if(events[i].startUtc>now){ g_nextEventUtc=events[i].startUtc; g_nextSummary=events[i].summary; nextIdx=(int)i; break; } }
  if(nextIdx>=0){
    uint32_t hz=0; String raw; bool haveFreq=getFreqForIndex((size_t)nextIdx,hz,raw);
    DBG("\n[Next] %s @ %s | freq_raw=\"%s\" -> %s%lu Hz\n",
        g_nextSummary.c_str(), fmtTimeLocalFull(g_nextEventUtc).c_str(),
        raw.c_str(), haveFreq?"":"(invalid) ", haveFreq?(unsigned long)hz:0UL);
  }
}

// ---------- Sprites ----------
void initAgent3SpriteMirroredLeft(){
  agent3Sprite.setColorDepth(16); agent3Sprite.createSprite(agent3_logo_WIDTH,agent3_logo_HEIGHT);
  agent3Sprite.setSwapBytes(true); agent3Sprite.fillSprite(agent3_logo_KEY_COLOR);
  for(int y=0;y<agent3_logo_HEIGHT;y++){ for(int x=0;x<agent3_logo_WIDTH;x++){ uint16_t c=pgm_read_word(&agent3_logo_data[y*agent3_logo_WIDTH+x]); agent3Sprite.drawPixel(agent3_logo_WIDTH-1-x,y,c); } }
}
void drawAgent3BottomLeft(){ agent3Sprite.pushSprite(2, tft.height()-agent3_logo_HEIGHT-2, agent3_logo_KEY_COLOR); }
void initDlbbSprite(){ dlbbSprite.setColorDepth(16); dlbbSprite.createSprite(dlbb_logo_WIDTH,dlbb_logo_HEIGHT); dlbbSprite.setSwapBytes(true); dlbbSprite.fillSprite(dlbb_logo_KEY_COLOR); dlbbSprite.pushImage(0,0,dlbb_logo_WIDTH,dlbb_logo_HEIGHT,dlbb_logo_data); }
void drawDlbbBottomRight(){ dlbbSprite.pushSprite(tft.width()-dlbb_logo_WIDTH-2, tft.height()-dlbb_logo_HEIGHT-2, dlbb_logo_KEY_COLOR); }

// ---------- CAT utils ----------
static inline uint8_t bcdbyte(uint8_t hi,uint8_t lo){ return ((hi&0x0F)<<4)|(lo&0x0F); }
void catLog5(uint8_t opcode,uint8_t p1=0,uint8_t p2=0,uint8_t p3=0,uint8_t p4=0){ DBG("[ %02X %02X %02X %02X %02X ]\n", p4,p3,p2,p1,opcode); }
void catSend5(uint8_t opcode,uint8_t p1=0,uint8_t p2=0,uint8_t p3=0,uint8_t p4=0){
#if FRG100
  DBG("CAT SEND: "); catLog5(opcode,p1,p2,p3,p4);
  uint8_t b[5]={p4,p3,p2,p1,opcode}; for(int i=0;i<5;i++){ CAT.write(b[i]); CAT.flush(); delay(5); }
#else
  (void)opcode; (void)p1; (void)p2; (void)p3; (void)p4;
#endif
}
void catPower(bool on){
#if FRG100
  if(g_catOn==on) return;
  DBG("CAT POWER %s ", on?"ON":"OFF");
  catSend5(0x20, on?0x01:0x00);
#endif
  g_catOn=on;
}
void catSetMode(uint8_t m){
#if FRG100
  if(g_catMode==m) return;
  DBG("CAT MODE %s ", m==0?"LSB":(m==1?"USB":"?"));
  catSend5(0x0C, m);
#endif
  g_catMode=m;
}
void catSetModeUSB(){ catSetMode(1); }
void catSetModeLSB(){ catSetMode(0); }
void catSetFreqHz(uint32_t hz){
#if FRG100
  if(g_catFreqHz==hz) return;
  uint8_t d1=(hz/10)%10, d2=(hz/100)%10, d3=(hz/1000)%10, d4=(hz/10000)%10, d5=(hz/100000)%10, d6=(hz/1000000)%10, d7=(hz/10000000)%10, d8=(hz/100000000)%10;
  uint8_t F1=bcdbyte(d8,d7), F2=bcdbyte(d6,d5), F3=bcdbyte(d4,d3), F4=bcdbyte(d2,d1);
  DBG("CAT FREQ %lu Hz ", (unsigned long)hz); catSend5(0x0A, F1,F2,F3,F4);
#endif
  g_catFreqHz=hz;
}
void catEnsureOff(){ if(g_catOn){ DBG("CAT Ensure OFF -> "); catPower(false);} }
void catEnsureOnUSB(){ if(!g_catOn){ DBG("CAT Ensure ON -> "); catPower(true);} if(g_catMode!=1){ DBG("CAT Ensure MODE USB -> "); catSetModeUSB(); } }

// ---------- UDP Helper ----------
void udpSendKHz(uint32_t hz) {
  uint32_t khz = hz / 1000U;
  char buf[16];
  #if DEBUG
    snprintf(buf, sizeof(buf), "%lu\n", (unsigned long)khz);
  #else
    snprintf(buf, sizeof(buf), "%lu", (unsigned long)khz);
  #endif
  g_udp.beginPacket(UDP_DST_IP, UDP_DST_PORT);
  g_udp.write((const uint8_t*)buf, strlen(buf));
  g_udp.endPacket();
  DBG("[UDP] %lu kHz -> %s\n", (unsigned long)khz, UDP_DST_IP.toString().c_str());
}

// ---------- Zeit/Sync + HTML-Extractor ----------
bool syncTimeBerlin(uint32_t timeoutMs=30000){
  ensureTZBerlin(); configTime(0,0,"pool.ntp.org","time.nist.gov","time.google.com");
  uint32_t t0=millis(); time_t now=0; struct tm info;
  while(millis()-t0<timeoutMs){ now=time(nullptr); if(now>1700000000){ ensureTZBerlin(); if(getLocalTime(&info,1000)) return true; } delay(500); }
  return false;
}
String extractDivValue(const String& html,const char* klass){
  String key=String("class=\"")+klass+"\""; int p=html.indexOf(key); if(p<0) return "";
  int tagStart=html.lastIndexOf('<',p); if(tagStart<0) return ""; int openEnd=html.indexOf('>',tagStart); if(openEnd<0) return "";
  int closeStart=html.indexOf("</",openEnd); if(closeStart<0) return ""; String inner=html.substring(openEnd+1,closeStart);
  inner.replace("&amp;","&"); inner.replace("&nbsp;"," "); inner.replace("&lt;","<"); inner.replace("&gt;",">"); inner.trim(); return inner;
}

// ---------- ISO8601 -> UTC ----------
bool parseIso8601ToUtc(const char* dtRaw, time_t& outUtc){
  if(!dtRaw||!*dtRaw) return false;
  String s(dtRaw);
  int dot=s.indexOf('.'); if(dot>=0){
    int z=s.indexOf('Z',dot),p=s.indexOf('+',dot),m=s.indexOf('-',dot),e=s.length();
    int ofs=(z>=0)?z:((p>=0)?p:((m>=0)?m:e));
    s.remove(dot,ofs-dot);
  }
  int tzSign=-1;
  for(int i=s.length()-1;i>=0;--i){
    if((s[i]=='+'||s[i]=='-')&&i>=19){ tzSign=i; break; }
    if(s[i]=='T') break;
  }
  String base=s; int offsSec=0;
  if(s.endsWith("Z")) base.remove(base.length()-1);
  else if(tzSign>=0){
    base=s.substring(0,tzSign);
    int sign=(s[tzSign]=='-')?-1:1; int hh=0,mm=0;
    if(tzSign+3<(int)s.length()) hh=(s[tzSign+1]-'0')*10+(s[tzSign+2]-'0');
    if(tzSign+6<=(int)s.length()&&s[tzSign+3]==':') mm=(s[tzSign+4]-'0')*10+(s[tzSign+5]-'0');
    offsSec=sign*(hh*3600+mm*60);
  }
  struct tm tmN={};
  if(!strptime(base.c_str(),"%Y-%m-%dT%H:%M:%S",&tmN)) return false;
  time_t t=timegm_compat(&tmN);
  t -= offsSec;
  outUtc=t; return true;
}

// ---------- Daten holen ----------
bool fetchTopEvents(std::vector<EventItem>& out){
  out.clear(); g_lastErr="";
  g_cal_time.clear(); g_cal_voice.clear(); g_cal_frequency.clear(); g_cal_mode.clear(); g_cal_remarks.clear();

  ensureTZBerlin();
  time_t nowUtc=time(nullptr); if(nowUtc<100000){ g_lastErr="Zeit unsynchron."; return false; }

  time_t timeMinUtc=nowUtc, timeMaxUtc=midnightBerlinFor(nowUtc);
  String minIso=iso8601Z_ms(timeMinUtc), maxIso=iso8601Z_ms(timeMaxUtc);
  String url=String(BASE_URL)+"?timeMin="+urlEncode(minIso)+"&timeMax="+urlEncode(maxIso);

  WiFiClientSecure client; client.setInsecure();
  HTTPClient http; http.setFollowRedirects(HTTPC_STRICT_FOLLOW_REDIRECTS);
  if(!http.begin(client,url)){ g_lastErr="HTTP begin fehlgeschlagen"; return false; }
  http.setUserAgent(UA_EDGE);
  http.addHeader("Accept","application/json,*/*;q=0.7");
  http.addHeader("Connection","keep-alive");
  http.addHeader("Cache-Control","no-cache");

  int code=http.GET();
  if(code<=0){ g_lastErr=String("HTTP Fehler: ")+http.errorToString(code); http.end(); return false; }
  String body=http.getString(); http.end();
  if(code!=HTTP_CODE_OK){ g_lastErr=String("HTTP Status ")+code; return false; }

  JsonDocument doc;
  DeserializationError err = deserializeJson(doc, body);
  if(err){ g_lastErr = String("JSON Fehler: ") + err.c_str(); return false; }

  JsonArray items = doc["items"].as<JsonArray>();
  if(items.isNull()){ g_lastErr="JSON: items[] fehlt"; return true; }

  for(JsonObject it : items){
    const char* sum = it["summary"].is<const char*>() ? it["summary"].as<const char*>() :
                      (it["title"].is<const char*>()   ? it["title"].as<const char*>()   : "");

    const char* dtRaw = nullptr;
    if(it["start"].is<JsonObject>()){
      JsonObject st = it["start"].as<JsonObject>();
      if(st["dateTime"].is<const char*>()) dtRaw = st["dateTime"];
      else if(st["date"].is<const char*>()) dtRaw = st["date"];
    } else {
      if(it["startTime"].is<const char*>()) dtRaw = it["startTime"];
      else if(it["start"].is<const char*>()) dtRaw = it["start"];
    }
    if(!dtRaw||!*dtRaw) continue;

    time_t startUtc=0;
    if(!parseIso8601ToUtc(dtRaw, startUtc)) continue;

    if(startUtc>=timeMinUtc && startUtc<=timeMaxUtc){
      g_events.push_back(EventItem{startUtc, String(sum)});

      String desc;
      if(it["description"].is<const char*>()) desc = String(it["description"].as<const char*>());
      else if(it["content"].is<const char*>()) desc = String(it["content"].as<const char*>());

      g_cal_time.push_back(     extractDivValue(desc,"calendar-time"));
      g_cal_voice.push_back(    extractDivValue(desc,"calendar-voice"));
      g_cal_frequency.push_back(extractDivValue(desc,"calendar-frequency"));
      g_cal_mode.push_back(     extractDivValue(desc,"calendar-mode"));
      g_cal_remarks.push_back(  extractDivValue(desc,"calendar-remarks"));
    }
  }

  // sort + Arrays passend umsortieren
  std::vector<size_t> idx(g_events.size());
  for(size_t i=0;i<idx.size();++i) idx[i]=i;
  std::sort(idx.begin(),idx.end(),[&](size_t a,size_t b){ return g_events[a].startUtc < g_events[b].startUtc; });

  auto reorder=[&](auto& vec){
    using T=typename std::remove_reference<decltype(vec)>::type::value_type;
    std::vector<T> tmp; tmp.reserve(vec.size());
    for(auto i:idx) tmp.push_back(vec[i]);
    vec.swap(tmp);
  };

  std::vector<EventItem> sorted; sorted.reserve(g_events.size());
  for(auto i:idx) sorted.push_back(g_events[i]);
  g_events.swap(sorted);

  reorder(g_cal_time); reorder(g_cal_voice); reorder(g_cal_frequency); reorder(g_cal_mode); reorder(g_cal_remarks);

  out = g_events;
  return true;
}

// ---------- Anzeige aus Cache ----------
static void drawFromCache(){ drawHeaderAndHudFrame(); drawEventsList(g_events,12); updateNextEventCache(g_events); drawAgent3BottomLeft(); updateClockHud(); drawDlbbBottomRight(); }

// ---------- showTop10 ----------
void showTop10(bool doFetch){
  bool ok=true;
  if(doFetch){ std::vector<EventItem> events; ok=fetchTopEvents(events); if(ok){ g_events=events; g_loadedOnce=true; g_nextRetryMs=0; } }
  if(!ok){
    drawHeaderAndHudFrame(); int y=listStartY()+8; tft.setTextFont(1); tft.setTextColor(TFT_RED,TFT_BLACK); tft.setTextSize(1);
    tft.setCursor(8,y); tft.print("Fehler beim Abruf/Parsing."); y+=18; tft.setCursor(8,y); tft.setTextColor(TFT_DARKGREY,TFT_BLACK); if(g_lastErr.length()) tft.print(g_lastErr);
    drawAgent3BottomLeft(); updateClockHud(); drawDlbbBottomRight(); g_nextRetryMs=millis()+10000; return;
  }
  drawFromCache();
}

// ---------- Setup ----------
void setup(){
  #if DEBUG
    Serial.begin(115200); delay(200);
  #endif
  ensureTZBerlin();

  tft.init(); tft.setRotation(1); tft.fillScreen(TFT_BLACK); drawHeaderAndHudFrame();
  initAgent3SpriteMirroredLeft(); initDlbbSprite(); initHudSprite();

#if FRG100
  CAT.begin(CAT_BAUD, CAT_SERIAL_CONF, /*rxPin=*/-1, /*txPin=*/CAT_TX_PIN);
#endif

  // WLAN
  tft.setTextFont(1); tft.setTextColor(TFT_WHITE,TFT_BLACK); tft.setTextSize(2);
  int msgY=listStartY()+8; tft.setCursor(8,msgY); tft.print("WLAN: Verbinden");
  WiFi.mode(WIFI_STA); WiFi.begin(WIFI_SSID, WIFI_PASSWORD);
  uint32_t t0=millis();
  while(WiFi.status()!=WL_CONNECTED && millis()-t0<20000){ delay(250); tft.print("."); }
  if(WiFi.status()==WL_CONNECTED){ tft.print(" OK"); DBG("IP: %s\n", WiFi.localIP().toString().c_str()); }
  else { tft.print(" FEHLER"); }

  // Zeit Sync
  tft.setCursor(8, msgY+20); tft.print("Zeit (Berlin): Sync…");
  bool timeOk=syncTimeBerlin(30000); if(timeOk){ tft.print(" OK"); } else { tft.print(" FEHLER"); }

  // UDP starten
  g_udp.begin(0);

  // Tagesliste einmal laden
  showTop10(true);

  // ATS-Test
#if ATS
  //DBG("\n[ATS] UDP-Test: 146, 6070, 11223 kHz (je 5 s)…\n");
  auto send_khz = [&](uint32_t k){ udpSendKHz(k * 1000U); delay(5000); };
  send_khz(3573); send_khz(7074); send_khz(14074); send_khz(21074); send_khz(28074);
  DBG("[ATS] Ende UDP-Test — weiter mit regulärem Betrieb.\n");
#endif
}

// ---------- Loop ----------
static String make_sig(std::vector<size_t> live){
  std::sort(live.begin(), live.end());
  String s;
  for(size_t i=0;i<live.size();++i){ if(i) s+="-"; s+=String((unsigned long)live[i]); }
  return s;
}

void loop(){
  static uint32_t lastHud=0; static time_t prevNowSec=0;
  uint32_t nowMs=millis(); time_t nowSec=time(nullptr);

  if(g_nextRetryMs && nowMs>=g_nextRetryMs) showTop10(true);

  // LIVE-Indizes mit gültiger QRG sammeln (Listenreihenfolge)
  std::vector<size_t> live;
  for (size_t i=0; i<g_events.size(); ++i) {
    time_t s = g_events[i].startUtc;
    if (nowSec >= s && nowSec < (s + LIVE_WINDOW_SEC)) {
      uint32_t hz=0; String raw;
      if (getFreqForIndex(i, hz, raw)) live.push_back(i);
    }
  }

  // Set-Wechsel erkennen -> Fenster & Rotation zurücksetzen
  String sig = make_sig(live);
  if (sig != g_liveSigPrev) {
    g_liveSigPrev = sig;
    g_windowStartMs = nowMs;
    g_rotActive = live.size() >= 2;
    g_rotCursor = 0;
    g_rotNextSwitchMs = nowMs; // sofort starten
    g_singleSent = false;
    DBG("[ROT] Neues Live-Set: %s (N=%u)\n", sig.c_str(), (unsigned)live.size());
  }

  // Nichts live -> CAT aus, nix zu tun
  if (live.empty()) {
#if FRG100
    catEnsureOff();
#endif
  } else {
    bool windowActive = (nowMs - g_windowStartMs) < 120000U; // 2 Minuten
    if (windowActive) {
      if (!g_rotActive) {
        // Einzelstation -> genau 1× senden
        if (!g_singleSent) {
          size_t idx = live[0];
          uint32_t hz=0; String raw;
          if (getFreqForIndex(idx, hz, raw)) {
            udpSendKHz(hz);
#if FRG100
            catEnsureOnUSB(); catSetFreqHz(hz);
#endif
            g_singleSent = true;
          }
        }
      } else {
        // Mehrere -> Rotation alle 5 s: 1., 2., 3., …, 1., 2., …
        if (nowMs >= g_rotNextSwitchMs) {
          size_t N = live.size();
          size_t idx = live[g_rotCursor % N];
          uint32_t hz=0; String raw;
          if (getFreqForIndex(idx, hz, raw)) {
            udpSendKHz(hz);
#if FRG100
            catEnsureOnUSB(); catSetFreqHz(hz);
#endif
          }
          g_rotCursor = (g_rotCursor + 1) % N;
          g_rotNextSwitchMs = nowMs + 5000U; // 5 s
        }
      }
    } else {
      // 2-Minuten-Fenster vorbei -> nichts mehr senden bis Set-Wechsel
    }
  }

  // HUD + Redraw
  if(nowMs-lastHud>=1000){
    lastHud=nowMs; updateClockHud();
    bool needRedraw=false;
    if(prevNowSec!=0){
      for(const auto& e: g_events){
        if(e.startUtc>prevNowSec && e.startUtc<=nowSec){ needRedraw=true; break; }
        time_t endMark=e.startUtc+LIVE_WINDOW_SEC;
        if(endMark>prevNowSec && endMark<=nowSec){ needRedraw=true; break; }
      }
    }
    prevNowSec=nowSec;
    if(needRedraw) drawFromCache();
  }
}
