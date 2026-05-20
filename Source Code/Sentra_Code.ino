/*
 * ╔══════════════════════════════════════════════════════════════════╗
 *   SENTRA CCTV v1.0 — DFRobot DFR1154  (ESP32-S3 / OV3660)
 * ╚══════════════════════════════════════════════════════════════════╝
 */

#include "esp_camera.h"
#include "ESP_I2S.h"           // official DFRobot audio library
#include "DFRobot_LTR308.h"    // install from Library Manager
#include <WiFi.h>
#include <WebServer.h>
#include <SD.h>
#include <Wire.h>
#include <time.h>
#include <math.h>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/semphr.h"
#include "freertos/queue.h"

// ═══════════════════════════════════════════════════════
//  USER CONFIG
// ═══════════════════════════════════════════════════════
#define WIFI_SSID "Your SSID"
#define WIFI_PASS "Your PASS"
#define TZ_OFFSET_SEC -28800 // UTC-8 Pacific Standard Time (PST)

// Battery: true only if voltage divider wired to GPIO44
// Remove Gravity RX cable first — GPIO44 = UART0 RX by default
#define BATTERY_WIRED   false
#define BAT_PIN         44
#define BAT_DIV         0.3197f   // 47k/(100k+47k)

// ═══════════════════════════════════════════════════════
//  PINS 
// ═══════════════════════════════════════════════════════
// Camera
#define CAM_PWDN   -1
#define CAM_RESET  -1
#define CAM_XCLK    5
#define CAM_SIOD    8
#define CAM_SIOC    9
#define CAM_D7      4
#define CAM_D6      6
#define CAM_D5      7
#define CAM_D4     14
#define CAM_D3     17
#define CAM_D2     21
#define CAM_D1     18
#define CAM_D0     16
#define CAM_VSYNC   1
#define CAM_HREF    2
#define CAM_PCLK   15

// Confirmed from app_httpd.cpp: #define LED_LEDC_GPIO 47
#define PIN_IR     47   // IR fill light — ledcAttach(47,5000,8) + ledcWrite
// Confirmed from 6_9.ino: pinMode(3,OUTPUT); digitalWrite(3,HIGH);
#define PIN_LED     3   // status LED — plain GPIO
#define SD_CS      10

// Confirmed from 5_2.ino: i2s1.setPins(45, 46, 42)
#define SPK_BCLK   45
#define SPK_LR     46
#define SPK_DOUT   42
// Confirmed from 5_2.ino: i2s.setPinsPdmRx(CLOCK_PIN=38, DATA_PIN=39)
#define MIC_CLK    38
#define MIC_DATA   39

// ═══════════════════════════════════════════════════════
//  TUNING
// ═══════════════════════════════════════════════════════
#define SAMPLE_RATE     16000   // from 5_2.ino: #define SAMPLE_RATE (16000)
#define STREAM_FPS      20
#define MOTION_FPS      5
#define JPEG_QUAL       10
#define NIGHT_LUX       80.0f
#define THRESH_PERSON   55
#define THRESH_ALERT    70
#define SD_ROLL_MB      400
#define SD_FULL_PCT     90

// IR LED: from app_httpd.cpp setupLedFlash
#define IR_FREQ         5000
#define IR_RESOLUTION   8       // 8-bit → 0-255 duty
#define IR_MAX_DUTY     255

// ═══════════════════════════════════════════════════════
//  I2S — two global instances
//  From 5_2.ino: I2SClass i2s; I2SClass i2s1;
//  i2s  (declared first)  → assigned I2S_NUM_0 → PDM mic
//  i2s1 (declared second) → assigned I2S_NUM_1 → speaker
// ═══════════════════════════════════════════════════════
static I2SClass i2s;    // PDM mic — MUST be declared first
static I2SClass i2s1;   // Speaker — MUST be declared second
static bool     mic_ok  = false;
static bool     spk_ok  = false;

// ═══════════════════════════════════════════════════════
//  ALS
// ═══════════════════════════════════════════════════════
static DFRobot_LTR308 light;
static bool als_ok = false;

// ═══════════════════════════════════════════════════════
//  GLOBAL STATE
// ═══════════════════════════════════════════════════════
WebServer server(80);

volatile float  g_motion    = 0.0f;
volatile float  g_lux       = 500.0f;
volatile float  g_sound     = 0.0f;
volatile float  g_vbat      = 0.0f;
volatile int    g_batPct    = -1;
volatile bool   g_night     = false;
volatile bool   g_irOn      = false;
volatile int    g_irDuty    = 0;
volatile bool   g_autoIR    = true;
volatile bool   g_recording = false;
volatile bool   g_alert     = false;
volatile bool   g_contMot   = false;
volatile bool   g_sdOK      = false;
char            g_act[12]   = "idle";
int             g_contCnt   = 0;
static float    g_sndSmooth = 0.0f;

static uint8_t* g_prev     = nullptr;
static size_t   g_prevLen  = 0;
static SemaphoreHandle_t mx_prev = nullptr;

static volatile bool g_strOn  = false;
static WiFiClient    g_strCli;

static File     g_avi;
static uint32_t g_aviFr = 0, g_aviMs = 0;
static SemaphoreHandle_t mx_sd = nullptr;
struct AviIdx { uint32_t off, sz; };
#define IDX_MAX 15000
static AviIdx*  g_idx  = nullptr;
static uint32_t g_idxN = 0;

#define EV_MAX 30
struct Ev { uint32_t ts; char msg[72]; };
static Ev  g_ev[EV_MAX];
static int g_evH = 0;
static SemaphoreHandle_t mx_ev = nullptr;

enum SpkT { BEEP_BOOT, BEEP_ALERT, BEEP_MOTION, BEEP_SIREN, SPK_ANNOUNCE };
struct SpkJob { SpkT type; char text[96]; };
static QueueHandle_t g_spkQ = nullptr;

// ═══════════════════════════════════════════════════════
//  UTILITY
// ═══════════════════════════════════════════════════════
static inline String B(bool v) { return v ? "true" : "false"; }

void evLog(const char* m) {
    if (mx_ev) xSemaphoreTake(mx_ev, portMAX_DELAY);
    g_ev[g_evH].ts = millis();
    strncpy(g_ev[g_evH].msg, m, 71);
    g_ev[g_evH].msg[71] = '\0';
    g_evH = (g_evH + 1) % EV_MAX;
    if (mx_ev) xSemaphoreGive(mx_ev);
    Serial.printf("[EV] %s\n", m);
}

String nowStr() {
    struct tm t;
    if (!getLocalTime(&t, 30)) {
        uint32_t s = millis()/1000;
        char b[12];
        snprintf(b, sizeof(b), "%02lu:%02lu:%02lu",
            (unsigned long)(s/3600),
            (unsigned long)((s%3600)/60),
            (unsigned long)(s%60));
        return String(b);
    }
    char b[20]; strftime(b, sizeof(b), "%H:%M:%S", &t);
    return String(b);
}

// ═══════════════════════════════════════════════════════
//  IR LED — from app_httpd.cpp (official CameraWebServer)
//  setupLedFlash: ledcAttach(pin, 5000, 8)
//  enable_led:    ledcWrite(LED_LEDC_GPIO, duty)
// ═══════════════════════════════════════════════════════
void irSetup() {
    // Exact pattern from app_httpd.cpp setupLedFlash():
    ledcAttach(PIN_IR, IR_FREQ, IR_RESOLUTION);
    ledcWrite(PIN_IR, 0);
    Serial.printf("[IR]  ledcAttach(GPIO%d, %d, %d) — official pattern\n",
                  PIN_IR, IR_FREQ, IR_RESOLUTION);
}

void irSetDuty(int duty) {
    if (duty < 0) duty = 0;
    if (duty > IR_MAX_DUTY) duty = IR_MAX_DUTY;
    g_irDuty = duty;
    g_irOn   = (duty > 0);
    // Exact pattern from app_httpd.cpp enable_led():
    ledcWrite(PIN_IR, duty);
}

// Lux to IR duty — darker = brighter
int luxToDuty(float lux) {
    if (lux >= NIGHT_LUX * 1.5f) return 0;
    if (lux <= 5.0f) return IR_MAX_DUTY;
    float ratio = (NIGHT_LUX * 1.5f - lux) / (NIGHT_LUX * 1.5f - 5.0f);
    return (int)(ratio * IR_MAX_DUTY);
}

// ═══════════════════════════════════════════════════════
//  BATTERY
// ═══════════════════════════════════════════════════════
void readBattery() {
    if (!BATTERY_WIRED) { g_vbat = 0; g_batPct = -1; return; }
    long sum = 0;
    for (int i = 0; i < 64; i++) { sum += analogRead(BAT_PIN); delayMicroseconds(200); }
    float v = (float)(sum/64) / 4095.0f * 3.3f / BAT_DIV;
    v = v < 2.8f ? 2.8f : v > 4.3f ? 4.3f : v;
    g_vbat = v;
    float p;
    if      (v >= 4.15f) p = 90 + (v-4.15f)/0.05f*10;
    else if (v >= 3.90f) p = 60 + (v-3.90f)/0.25f*30;
    else if (v >= 3.70f) p = 30 + (v-3.70f)/0.20f*30;
    else if (v >= 3.50f) p = 10 + (v-3.50f)/0.20f*20;
    else                  p = (v-2.8f)/0.70f*10;
    g_batPct = (int)(p < 0 ? 0 : p > 100 ? 100 : p);
}

// ═══════════════════════════════════════════════════════
//  CAMERA — from 6_9.ino / camera.h
// ═══════════════════════════════════════════════════════
bool initCamera() {
    camera_config_t config;
    config.ledc_channel = LEDC_CHANNEL_0;
    config.ledc_timer   = LEDC_TIMER_0;
    config.pin_d0       = CAM_D0;
    config.pin_d1       = CAM_D1;
    config.pin_d2       = CAM_D2;
    config.pin_d3       = CAM_D3;
    config.pin_d4       = CAM_D4;
    config.pin_d5       = CAM_D5;
    config.pin_d6       = CAM_D6;
    config.pin_d7       = CAM_D7;
    config.pin_xclk     = CAM_XCLK;
    config.pin_pclk     = CAM_PCLK;
    config.pin_vsync    = CAM_VSYNC;
    config.pin_href     = CAM_HREF;
    config.pin_sccb_sda = CAM_SIOD;
    config.pin_sccb_scl = CAM_SIOC;
    config.pin_pwdn     = CAM_PWDN;
    config.pin_reset    = CAM_RESET;
    config.xclk_freq_hz = 20000000;
    config.pixel_format = PIXFORMAT_JPEG;
    config.grab_mode    = CAMERA_GRAB_LATEST;
    config.fb_location  = CAMERA_FB_IN_PSRAM;
    config.jpeg_quality = JPEG_QUAL;
    config.fb_count     = 2;
    config.frame_size   = FRAMESIZE_VGA;
    esp_err_t err = esp_camera_init(&config);
    if (err != ESP_OK) {
        Serial.printf("[CAM] Init failed 0x%x\n", err);
        return false;
    }
    // from 6_9.ino sensor setup:
    sensor_t* s = esp_camera_sensor_get();
    if (s && s->id.PID == OV3660_PID) {
        s->set_vflip(s, 1);
        s->set_brightness(s, 1);
        s->set_saturation(s, -2);
    }
    return true;
}

// ═══════════════════════════════════════════════════════
//  ALS — from 5_1.ino
//  Comment: "initialize camera BEFORE LTR308"
// ═══════════════════════════════════════════════════════
void initALS() {
    Wire.begin(CAM_SIOD, CAM_SIOC);
    // From 5_1.ino: while(!light.begin()) { delay(1000); }
    int tries = 0;
    while (!light.begin() && tries < 5) {
        Serial.println("[ALS] Initialization failed! retrying...");
        delay(1000);
        tries++;
    }
    if (tries < 5) {
        als_ok = true;
        Serial.println("[ALS] Initialization successful!");
    } else {
        Serial.println("[ALS] Not found — using 500lx fallback");
    }
}

float readLux() {
    if (!als_ok) return 500.0f;
    uint32_t data = light.getData();
    float lux = light.getLux(data);
    return lux < 0.0f ? 0.0f : lux;
}

// ═══════════════════════════════════════════════════════
//  I2S MIC — from 5_2.ino exact pattern
// ═══════════════════════════════════════════════════════
void initMic() {
    // From 5_2.ino:
    // i2s.setPinsPdmRx(CLOCK_PIN, DATA_PIN);  CLOCK=38, DATA=39
    // i2s.begin(I2S_MODE_PDM_RX, SAMPLE_RATE, I2S_DATA_BIT_WIDTH_16BIT, I2S_SLOT_MODE_MONO)
    i2s.setPinsPdmRx(MIC_CLK, MIC_DATA);
    if (!i2s.begin(I2S_MODE_PDM_RX, SAMPLE_RATE,
                   I2S_DATA_BIT_WIDTH_16BIT, I2S_SLOT_MODE_MONO)) {
        Serial.println("[MIC] Failed to initialize I2S PDM RX");
        return;
    }
    mic_ok = true;
    Serial.println("[MIC] PDM RX OK (I2S_NUM_0)");
}

// ═══════════════════════════════════════════════════════
//  I2S SPEAKER — from 5_2.ino exact pattern
// ═══════════════════════════════════════════════════════
void initSpeaker() {
    // From 5_2.ino:
    // i2s1.setPins(45, 46, 42)
    // i2s1.begin(I2S_MODE_STD, SAMPLE_RATE, I2S_DATA_BIT_WIDTH_16BIT, I2S_SLOT_MODE_MONO)
    i2s1.setPins(SPK_BCLK, SPK_LR, SPK_DOUT);
    if (!i2s1.begin(I2S_MODE_STD, SAMPLE_RATE,
                    I2S_DATA_BIT_WIDTH_16BIT, I2S_SLOT_MODE_MONO)) {
        Serial.println("[SPK] MAX98357 initialization failed!");
        return;
    }
    spk_ok = true;
    Serial.println("[SPK] MAX98357 OK (I2S_NUM_1)");
}

// ═══════════════════════════════════════════════════════
//  MIC LEVEL — RMS + EMA smoothing
// ═══════════════════════════════════════════════════════
float readMicLevel() {
    if (!mic_ok) return 0.0f;
    const int N = 512;
    int16_t buf[N];
    size_t got = i2s.readBytes((char*)buf, N * 2);
    if (got < 2) return g_sndSmooth;
    int n = (int)(got / 2);
    double sum = 0.0;
    for (int i = 0; i < n; i++) sum += (double)buf[i] * (double)buf[i];
    float rms = (float)sqrt(sum / (double)n);
    float pct = rms / 32768.0f * 100.0f * 4.0f;   // ×4 for sensitivity
    if (pct > 100.0f) pct = 100.0f;
    g_sndSmooth = g_sndSmooth * 0.75f + pct * 0.25f;  // EMA α=0.25
    return g_sndSmooth;
}

// ═══════════════════════════════════════════════════════
//  AUDIO ENGINE
//
//  ROOT CAUSE OF ANNOUNCEMENT NOT WORKING:
//  playWAV() internally calls configureTX() every time it
//  is called. configureTX() tears down and rebuilds the I2S
//  TX DMA channel. For small buffers (beeps) this is fast
//  enough that it works. For large buffers (announcement,
//  several seconds), the DMA channel setup times out
//  internally and write() is never called — silence.
//
//  THE FIX: Use i2s1.write(raw_pcm_bytes, size) DIRECTLY.
//  This writes to the already-configured DMA channel with
//  no header parsing, no configureTX, no channel teardown.
//  The channel is configured ONCE in initSpeaker() and
//  stays configured for the lifetime of the program.
//  Every audio output function uses write() only.
// ═══════════════════════════════════════════════════════

// Write raw PCM directly to speaker DMA — THE core output function
static void spkWrite(const int16_t* pcm, int nSamples) {
    if (!spk_ok || !pcm || nSamples <= 0) return;
    // i2s1.write() takes uint8_t* and byte count
    i2s1.write((const uint8_t*)pcm, (size_t)nSamples * 2);
}

// Generate and play a sine tone in small stack-safe chunks
// No PSRAM allocation needed for simple tones
static void playTone(float freq, int ms, float amp) {
    if (!spk_ok) return;
    const int CHUNK = 256;  // samples per chunk — stack safe
    int16_t buf[CHUNK];
    int totalSamples = (SAMPLE_RATE * ms) / 1000;
    int sent = 0;
    while (sent < totalSamples) {
        int n = totalSamples - sent;
        if (n > CHUNK) n = CHUNK;
        for (int i = 0; i < n; i++) {
            float ph = 2.0f * M_PI * freq * (float)(sent + i) / (float)SAMPLE_RATE;
            buf[i] = (int16_t)(sinf(ph) * amp);
        }
        spkWrite(buf, n);
        sent += n;
    }
}

// Flush DMA — write silence to push last samples out
static void spkFlush() {
    if (!spk_ok) return;
    int16_t sil[256] = {0};
    spkWrite(sil, 256);
}

// ─── Boot chime ───────────────────────────────────────
void doBeepBoot() {
    playTone(440,  80, 20000.0f);
    playTone(660,  80, 20000.0f);
    playTone(880, 150, 20000.0f);
    spkFlush();
}

// ─── Alert beep ───────────────────────────────────────
void doBeepAlert() {
    for (int i = 0; i < 3; i++) {
        playTone(1000, 130, 26000.0f);
        // Brief silence between beeps
        int16_t sil[320] = {0}; spkWrite(sil, 320);
    }
    spkFlush();
}

// ─── Motion beep ──────────────────────────────────────
void doBeepMotion() {
    playTone(700,  90, 22000.0f);
    playTone(950, 110, 22000.0f);
    spkFlush();
}

// ─── SIREN — 3 full seconds, maximum volume ───────────
// Builds in PSRAM, writes via spkWrite (raw PCM, no header)
void doSiren() {
    if (!spk_ok) return;
    const int N = SAMPLE_RATE * 3; // 48000 samples = 3 seconds
    int16_t* pcm = (int16_t*)heap_caps_malloc(N * 2, MALLOC_CAP_SPIRAM);
    if (!pcm) {
        // Fallback without PSRAM — chunked generation
        for (int chunk = 0; chunk < 3; chunk++) {
            for (int ms = 0; ms < 1000; ms += 50) {
                float f = 800.0f + 400.0f * (float)(chunk * 1000 + ms) / 3000.0f;
                playTone(f, 50, 32760.0f);
            }
        }
        return;
    }
    // Generate 800→1200 Hz sweep at int16 maximum amplitude
    for (int i = 0; i < N; i++) {
        float f  = 800.0f + 400.0f * (float)i / (float)N;
        float ph = 2.0f * M_PI * f * (float)i / (float)SAMPLE_RATE;
        pcm[i]   = (int16_t)(sinf(ph) * 32760.0f);
    }
    Serial.printf("[SPK] Siren: %d samples → spkWrite\n", N);
    spkWrite(pcm, N);
    heap_caps_free(pcm);
    spkFlush();
}

// ─── ANNOUNCEMENT — voiced formant synthesis ──────────
//
// How it produces speech-like sound vs a beep:
//   Each word gets a UNIQUE fundamental frequency (f0)
//   derived from the sum of its ASCII values. This unique
//   pitch per word is what makes it sound like distinct
//   syllables rather than a repeating beep.
//   Sawtooth wave (not sine) + 2 harmonics = voiced quality.
//   ADSR envelope = natural attack and release per word.
//
// Output: raw PCM written via spkWrite() — no WAV header,
// no playWAV(), no configureTX() resets.
void doAnnounce(const char* text) {
    if (!spk_ok || !text || !text[0]) return;

    int wc = 1;
    for (int i = 0; text[i]; i++) if (text[i] == ' ') wc++;
    if (wc > 20) wc = 20;

    // Buffer: intro + per-word + outro
    // 300ms intro + wc*(560ms word + 90ms gap) + 300ms outro
    int maxN = (SAMPLE_RATE / 1000) * (300 + wc*(560+90) + 300);
    if (maxN > SAMPLE_RATE * 15) maxN = SAMPLE_RATE * 15;

    int16_t* pcm = (int16_t*)heap_caps_malloc(maxN * 2, MALLOC_CAP_SPIRAM);
    if (!pcm) {
        Serial.println("[SPK] Announce: PSRAM alloc failed");
        doBeepAlert(); return;
    }
    memset(pcm, 0, maxN * 2);
    int pos = 0;

    // Write silence into pcm buffer
    auto sil = [&](int ms) {
        int n = (SAMPLE_RATE * ms) / 1000;
        if (pos + n > maxN) n = maxN - pos;
        memset(pcm + pos, 0, n * 2);
        pos += n;
    };

    // Write sine tone into pcm buffer (local phase counter)
    auto tone = [&](float freq, int ms, float amp) {
        int n = (SAMPLE_RATE * ms) / 1000;
        if (pos + n > maxN) n = maxN - pos;
        for (int i = 0; i < n && pos < maxN; i++) {
            float ph = 2.0f * M_PI * freq * (float)i / (float)SAMPLE_RATE;
            pcm[pos++] = (int16_t)(sinf(ph) * amp);
        }
    };

    // Intro chime — 3 rising tones clearly mark start of speech
    // These sound DIFFERENT from alert beeps (different freqs + spacing)
    tone(660, 65, 9000.0f);  sil(12);
    tone(880, 65, 9000.0f);  sil(12);
    tone(1100, 90, 8500.0f); sil(70);

    // Process words
    char tmp[96]; strncpy(tmp, text, 95); tmp[95] = '\0';
    char* sv; char* word = strtok_r(tmp, " ", &sv);
    int wi = 0;
    while (word && wi < 20 && pos < maxN) {
        int wlen = (int)strlen(word);
        if (!wlen) { word = strtok_r(nullptr, " ", &sv); continue; }

        // Unique f0 per word — this is what makes each word
        // sound different from the others (not just same beep)
        int cs = 0;
        for (int i = 0; i < wlen; i++) cs += toupper((unsigned char)word[i]);
        float f0 = 120.0f + (float)(cs % 120);   // 120–240 Hz
        float f1 = f0 * 3.0f;   // 1st formant
        float f2 = f0 * 5.0f;   // 2nd formant (brightness)

        int durMs = 180 + wlen * 24;
        if (durMs > 520) durMs = 520;
        int N = (SAMPLE_RATE * durMs) / 1000;
        if (pos + N > maxN) N = maxN - pos;

        for (int i = 0; i < N && pos < maxN; i++) {
            float t = (float)i / (float)N;
            // ADSR envelope
            float env;
            if      (t < 0.06f) env = t / 0.06f;
            else if (t < 0.18f) env = 1.0f - (t-0.06f)/0.12f * 0.18f;
            else if (t < 0.80f) env = 0.82f;
            else                 env = 0.82f * (1.0f-(t-0.80f)/0.20f);
            // Natural pitch fall per word
            float pitch = 1.0f - t * 0.06f;
            // Sawtooth harmonics — voiced character (NOT sine = not beep)
            float p0 = fmodf((float)i * f0 * pitch / (float)SAMPLE_RATE, 1.0f);
            float p1 = fmodf((float)i * f1 * pitch / (float)SAMPLE_RATE, 1.0f);
            float p2 = fmodf((float)i * f2 * pitch / (float)SAMPLE_RATE, 1.0f);
            float s  = (2.0f*p0-1.0f)*0.55f
                     + (2.0f*p1-1.0f)*0.28f
                     + (2.0f*p2-1.0f)*0.17f;
            pcm[pos++] = (int16_t)(s * env * 22000.0f);
        }
        sil(85); // gap between words
        word = strtok_r(nullptr, " ", &sv);
        wi++;
    }

    // Outro chime
    tone(880, 60, 7000.0f); sil(12); tone(660, 90, 6500.0f); sil(100);

    // Write entire announcement as raw PCM — NO playWAV, NO header
    Serial.printf("[SPK] Announce: %d words, %d samples (%.2fs) → spkWrite\n",
                  wi, pos, (float)pos / (float)SAMPLE_RATE);
    spkWrite(pcm, pos);
    heap_caps_free(pcm);
    spkFlush();
}

// ═══════════════════════════════════════════════════════
//  SPEAKER TASK — Core 1, priority 2
//  loop()/HTTP = Core 1, priority 1
//  100ms queue timeout keeps watchdog fed
// ═══════════════════════════════════════════════════════
void spkTask(void*) {
    SpkJob job;
    while (true) {
        if (xQueueReceive(g_spkQ, &job, pdMS_TO_TICKS(100)) == pdTRUE) {
            if (!spk_ok) { vTaskDelay(1); continue; }
            switch (job.type) {
                case BEEP_BOOT:    doBeepBoot();        break;
                case BEEP_ALERT:   doBeepAlert();       break;
                case BEEP_MOTION:  doBeepMotion();      break;
                case BEEP_SIREN:   doSiren();           break;
                case SPK_ANNOUNCE: doAnnounce(job.text);break;
            }
        }
        vTaskDelay(1);
    }
}

void qSpk(SpkT t, const char* txt = "") {
    if (!g_spkQ) return;
    SpkJob j; j.type = t;
    strncpy(j.text, txt, 95); j.text[95] = '\0';
    xQueueSend(g_spkQ, &j, 0);
}

// ═══════════════════════════════════════════════════════
//  MOTION DETECTION
// ═══════════════════════════════════════════════════════
float motionCalc(const uint8_t* cur, size_t clen) {
    if (!g_prev || !g_prevLen || !clen) return 0.0f;
    const size_t SKIP = 600; const int N = 512;
    size_t minL = clen < g_prevLen ? clen : g_prevLen;
    if (minL <= SKIP) return 0.0f;
    size_t step = (minL - SKIP) / (size_t)N;
    if (step < 1) step = 1;
    long diff = 0;
    for (int i = 0; i < N; i++) {
        size_t idx = SKIP + (size_t)i * step;
        if (idx >= clen || idx >= g_prevLen) break;
        int d = (int)cur[idx] - (int)g_prev[idx];
        diff += d < 0 ? -d : d;
    }
    float p = (float)diff / 80.0f;
    return p > 100.0f ? 100.0f : p;
}

// ═══════════════════════════════════════════════════════
//  SMART ENGINE — lux drives IR, day/night, alerts
// ═══════════════════════════════════════════════════════
static bool prevAlert = false, prevPerson = false;

void runEngine(float motion, float lux, float sound) {
    g_sound = sound; g_lux = lux;

    // Day/Night with hysteresis (80lx on, 120lx off)
    if (lux < NIGHT_LUX)           g_night = true;
    if (lux > NIGHT_LUX * 1.5f)    g_night = false;

    // Auto IR LED — brightness proportional to darkness
    if (g_autoIR) {
        int duty = g_night ? luxToDuty(lux) : 0;
        if (duty != g_irDuty) irSetDuty(duty);
    }

    // Continuous motion
    if (motion > 10.0f) {
        if (++g_contCnt >= 10 && !g_contMot) {
            g_contMot = true; evLog("Continuous motion");
        }
    } else { g_contCnt = 0; g_contMot = false; }

    // Activity
    if      (motion >= (float)THRESH_PERSON) strcpy(g_act, "person");
    else if (motion > 10.0f)                  strcpy(g_act, "motion");
    else                                       strcpy(g_act, "idle");

    bool newAlert  = (motion >= (float)THRESH_ALERT);
    bool isPerson  = (motion >= (float)THRESH_PERSON);
    if (newAlert  && !prevAlert)  { evLog("ALERT: High motion"); qSpk(BEEP_ALERT);  }
    if (isPerson  && !prevPerson) { evLog("Person detected");    qSpk(BEEP_MOTION); }
    prevAlert  = newAlert;  prevPerson = isPerson;
    g_alert    = newAlert;  g_motion   = motion;
}

// ═══════════════════════════════════════════════════════
//  SENSOR TASK — Core 0, priority 3
// ═══════════════════════════════════════════════════════
void sensorTask(void*) {
    const TickType_t intv = pdMS_TO_TICKS(1000 / MOTION_FPS);
    uint32_t batTimer = 0;
    while (true) {
        TickType_t t0 = xTaskGetTickCount();
        camera_fb_t* fb = esp_camera_fb_get();
        if (fb) {
            float lux    = readLux();
            float sound  = readMicLevel();
            float motion = motionCalc(fb->buf, fb->len);
            runEngine(motion, lux, sound);
            if (xSemaphoreTake(mx_prev, pdMS_TO_TICKS(10)) == pdTRUE) {
                if (fb->len != g_prevLen) {
                    heap_caps_free(g_prev);
                    g_prev    = (uint8_t*)heap_caps_malloc(fb->len, MALLOC_CAP_SPIRAM);
                    g_prevLen = g_prev ? fb->len : 0;
                }
                if (g_prev) memcpy(g_prev, fb->buf, fb->len);
                xSemaphoreGive(mx_prev);
            }
            esp_camera_fb_return(fb);
        }
        if (millis() - batTimer > 15000) { readBattery(); batTimer = millis(); }
        TickType_t elapsed = xTaskGetTickCount() - t0;
        if (elapsed < intv) vTaskDelay(intv - elapsed);
    }
}

// ═══════════════════════════════════════════════════════
//  AVI RECORDING
// ═══════════════════════════════════════════════════════
static void w32(File& f,uint32_t v){uint8_t b[4]={(uint8_t)v,(uint8_t)(v>>8),(uint8_t)(v>>16),(uint8_t)(v>>24)};f.write(b,4);}
static void w16(File& f,uint16_t v){uint8_t b[2]={(uint8_t)v,(uint8_t)(v>>8)};f.write(b,2);}
#define MOVI_OFF 212
void aviHdr(File& f,uint32_t w,uint32_t h,uint32_t fps){
    f.write((const uint8_t*)"RIFF",4);w32(f,0);f.write((const uint8_t*)"AVI ",4);
    f.write((const uint8_t*)"LIST",4);w32(f,192);f.write((const uint8_t*)"hdrl",4);
    f.write((const uint8_t*)"avih",4);w32(f,56);
    w32(f,1000000/fps);w32(f,0);w32(f,0);w32(f,0x10);
    w32(f,0);w32(f,0);w32(f,1);w32(f,0);w32(f,w);w32(f,h);w32(f,0);w32(f,0);w32(f,0);w32(f,0);
    f.write((const uint8_t*)"LIST",4);w32(f,116);f.write((const uint8_t*)"strl",4);
    f.write((const uint8_t*)"strh",4);w32(f,56);f.write((const uint8_t*)"vids",4);f.write((const uint8_t*)"MJPG",4);
    w32(f,0);w32(f,0);w32(f,0);w32(f,1);w32(f,fps);w32(f,0);w32(f,0);w32(f,0);w32(f,0);w32(f,0);
    w16(f,0);w16(f,0);w16(f,(uint16_t)w);w16(f,(uint16_t)h);
    f.write((const uint8_t*)"strf",4);w32(f,40);w32(f,40);w32(f,w);w32(f,h);
    w16(f,1);w16(f,24);f.write((const uint8_t*)"MJPG",4);
    w32(f,w*h*3);w32(f,0);w32(f,0);w32(f,0);w32(f,0);
    f.write((const uint8_t*)"LIST",4);w32(f,4);f.write((const uint8_t*)"movi",4);
}
void aviClose(File& f,uint32_t fr,uint32_t fps){
    uint32_t sz=f.size();
    f.seek(4);w32(f,sz-8);f.seek(48);w32(f,fr);f.seek(140);w32(f,fr);
    f.seek(MOVI_OFF);w32(f,sz-MOVI_OFF-4+4);
    f.seek(0,SeekEnd);
    f.write((const uint8_t*)"idx1",4);w32(f,g_idxN*16);
    for(uint32_t i=0;i<g_idxN;i++){f.write((const uint8_t*)"00dc",4);w32(f,0x10);w32(f,g_idx[i].off);w32(f,g_idx[i].sz);}
    f.close();
}
void startAVI(){
    if(!g_sdOK||g_recording)return;
    uint64_t tot=SD.totalBytes(),used=SD.usedBytes();
    if(tot>0&&used*100/tot>=SD_FULL_PCT){
        File r=SD.open("/");if(r){String old="";uint32_t oT=0xFFFFFFFF;
            File e=r.openNextFile();while(e){String n="/"+String(e.name());
                if(n.endsWith(".avi")){uint32_t t=e.getLastWrite();if(t<oT){oT=t;old=n;}}
                e=r.openNextFile();}r.close();if(old.length())SD.remove(old.c_str());}
    }
    if(!g_idx)g_idx=(AviIdx*)heap_caps_malloc(IDX_MAX*sizeof(AviIdx),MALLOC_CAP_SPIRAM);
    g_idxN=0;char name[40];snprintf(name,sizeof(name),"/rec%lu.avi",millis());
    if(xSemaphoreTake(mx_sd,pdMS_TO_TICKS(500))!=pdTRUE)return;
    g_avi=SD.open(name,FILE_WRITE);
    if(!g_avi){xSemaphoreGive(mx_sd);return;}
    aviHdr(g_avi,640,480,STREAM_FPS);g_aviFr=0;g_aviMs=millis();g_recording=true;
    xSemaphoreGive(mx_sd);evLog(("REC:"+String(name)).c_str());
}
void stopAVI(){
    if(!g_recording)return;
    if(xSemaphoreTake(mx_sd,pdMS_TO_TICKS(1000))!=pdTRUE)return;
    uint32_t ms=millis()-g_aviMs;
    uint32_t fps=(ms>0&&g_aviFr>0)?g_aviFr*1000/ms:STREAM_FPS;
    fps=fps<1?1:fps>30?30:fps;
    aviClose(g_avi,g_aviFr,fps);g_recording=false;xSemaphoreGive(mx_sd);evLog("Rec stopped");
}
void recFrame(const uint8_t* d,size_t len){
    if(!g_recording||!g_sdOK)return;
    if(xSemaphoreTake(mx_sd,pdMS_TO_TICKS(12))!=pdTRUE)return;
    uint32_t off=(uint32_t)(g_avi.position()-MOVI_OFF-8);
    g_avi.write((const uint8_t*)"00dc",4);w32(g_avi,(uint32_t)len);
    g_avi.write(d,len);if(len&1)g_avi.write((uint8_t)0);
    if(g_idxN<IDX_MAX){g_idx[g_idxN].off=off;g_idx[g_idxN].sz=(uint32_t)len;g_idxN++;}
    g_aviFr++;xSemaphoreGive(mx_sd);
    if(g_avi.size()>(uint32_t)SD_ROLL_MB*1024UL*1024UL){stopAVI();startAVI();}
}

// ═══════════════════════════════════════════════════════
//  STREAM TASK — Core 0, priority 5
// ═══════════════════════════════════════════════════════
void streamTask(void*) {
    const TickType_t intv = pdMS_TO_TICKS(1000/STREAM_FPS);
    TickType_t last = 0;
    while (true) {
        if (!g_strOn) { vTaskDelay(pdMS_TO_TICKS(40)); continue; }
        if (!g_strCli.connected()) {
            g_strOn = false; evLog("Stream disc");
            vTaskDelay(pdMS_TO_TICKS(100)); continue;
        }
        TickType_t now = xTaskGetTickCount();
        if ((now-last) < intv) vTaskDelay(intv-(now-last));
        last = xTaskGetTickCount();
        camera_fb_t* fb = esp_camera_fb_get();
        if (!fb) { vTaskDelay(10); continue; }
        recFrame(fb->buf, fb->len);
        char hdr[128];
        int hl = snprintf(hdr, sizeof(hdr),
            "--frame\r\nContent-Type: image/jpeg\r\nContent-Length: %u\r\n\r\n",
            (unsigned)fb->len);
        bool ok = (g_strCli.write((const uint8_t*)hdr, hl) == (size_t)hl);
        if (ok) ok = (g_strCli.write(fb->buf, fb->len) == fb->len);
        if (ok) g_strCli.write((const uint8_t*)"\r\n", 2);
        esp_camera_fb_return(fb);
        if (!ok) { g_strOn = false; evLog("Stream err"); }
    }
}

// ═══════════════════════════════════════════════════════
//  HTTP HANDLERS
// ═══════════════════════════════════════════════════════
void sendCors() {
    server.sendHeader("Access-Control-Allow-Origin",  "*");
    server.sendHeader("Access-Control-Allow-Methods", "GET,POST,OPTIONS");
    server.sendHeader("Access-Control-Allow-Headers", "Content-Type,Authorization");
    server.sendHeader("Cache-Control", "no-cache,no-store");
}
void handleOptions() { sendCors(); server.send(204); }
void handleRoot()    { sendCors(); server.send(200, "text/plain",
    "SENTINEL v11.0 — " + WiFi.localIP().toString()); }

void handleStream() {
    if (g_strOn) { sendCors(); server.send(409,"text/plain","busy"); return; }
    WiFiClient c = server.client(); c.setNoDelay(true);
    c.print("HTTP/1.1 200 OK\r\n"
            "Content-Type: multipart/x-mixed-replace; boundary=frame\r\n"
            "Access-Control-Allow-Origin: *\r\nCache-Control: no-cache\r\n"
            "Connection: keep-alive\r\n\r\n");
    c.flush(); g_strCli = c; g_strOn = true; evLog("Stream ON");
}

void handleSnapshot() {
    camera_fb_t* fb = esp_camera_fb_get();
    if (!fb) { server.send(503,"text/plain","cam error"); return; }
    if (g_sdOK && xSemaphoreTake(mx_sd,pdMS_TO_TICKS(300))==pdTRUE) {
        char n[40]; snprintf(n,sizeof(n),"/snap%lu.jpg",millis());
        File f=SD.open(n,FILE_WRITE); if(f){f.write(fb->buf,fb->len);f.close();}
        xSemaphoreGive(mx_sd);
    }
    sendCors();
    server.sendHeader("Content-Disposition","inline; filename=snap.jpg");
    server.send_P(200,"image/jpeg",(const char*)fb->buf,fb->len);
    esp_camera_fb_return(fb);
}

void handleData() {
    if (xSemaphoreTake(mx_ev,pdMS_TO_TICKS(60))!=pdTRUE) {
        server.send(503,"text/plain","busy"); return;
    }
    String ev="["; bool first=true;
    for (int i=0;i<EV_MAX;i++) {
        int idx=((g_evH-1-i)+EV_MAX)%EV_MAX;
        if(!g_ev[idx].ts)continue;
        if(!first)ev+=','; first=false;
        String m=String(g_ev[idx].msg); m.replace("\"","'");
        ev+="{\"ts\":"+String(g_ev[idx].ts)+",\"msg\":\""+m+"\"}";
        if(i>=9)break;
    }
    ev+="]"; xSemaphoreGive(mx_ev);
    uint64_t sdF=0,sdT=0;
    if(g_sdOK){sdF=SD.totalBytes()-SD.usedBytes();sdT=SD.totalBytes();}
    String bat = (g_batPct<0)
        ? "\"vbat\":0,\"batPct\":-1,"
        : "\"vbat\":"+String(g_vbat,2)+",\"batPct\":"+String(g_batPct)+",";
    String json="{";
    json+="\"motion\":"      +String(g_motion,1)+",";
    json+="\"activity\":\""  +String(g_act)+"\",";
    json+="\"lux\":"         +String(g_lux,1)+",";
    json+="\"sound\":"       +String(g_sound,1)+",";
    json+="\"night\":"       +B(g_night)+",";
    json+="\"ir\":"          +B(g_irOn)+",";
    json+="\"irDuty\":"      +String(g_irDuty)+",";
    json+="\"autoIR\":"      +B(g_autoIR)+",";
    json+="\"recording\":"   +B(g_recording)+",";
    json+="\"alert\":"       +B(g_alert)+",";
    json+="\"continuous\":"  +B(g_contMot)+",";
    json+="\"spkReady\":"    +B(spk_ok)+",";
    json+="\"micReady\":"    +B(mic_ok)+",";
    json+="\"alsReady\":"    +B(als_ok)+",";
    json+=bat;
    json+="\"batWired\":"    +B(BATTERY_WIRED)+",";
    json+="\"sdFreeGB\":"    +String((float)sdF/1073741824.0f,2)+",";
    json+="\"sdTotalGB\":"   +String((float)sdT/1073741824.0f,2)+",";
    json+="\"timestamp\":\"" +nowStr()+"\",";
    json+="\"uptime\":"      +String(millis()/1000UL)+",";
    json+="\"events\":"      +ev+"}";
    sendCors(); server.send(200,"application/json",json);
}

// handleControl returns IMMEDIATELY — audio queued in background
void handleControl() {
    sendCors();
    if (!server.hasArg("cmd")) {
        server.send(400,"application/json","{\"ok\":false,\"error\":\"no cmd\"}");
        return;
    }
    String cmd = server.arg("cmd");
    Serial.printf("[CTRL] cmd='%s'\n", cmd.c_str());
    bool ok = true;

    if      (cmd=="record/start") { if(!g_recording) startAVI(); }
    else if (cmd=="record/stop")  { if(g_recording)  stopAVI();  }
    else if (cmd=="ir/on")        { g_autoIR=false; irSetDuty(IR_MAX_DUTY); evLog("IR on (manual)"); }
    else if (cmd=="ir/off")       { g_autoIR=false; irSetDuty(0);           evLog("IR off (manual)");}
    else if (cmd=="autoIR/on")    { g_autoIR=true;  evLog("Auto-IR on"); }
    else if (cmd=="autoIR/off")   { g_autoIR=false; evLog("Auto-IR off");}
    else if (cmd=="siren/on")     { qSpk(BEEP_SIREN); evLog("SIREN"); }
    else if (cmd=="announce") {
        String t = server.hasArg("text") ? server.arg("text") : "";
        t.trim();
        if (t.length()>0 && t.length()<96) {
            qSpk(SPK_ANNOUNCE, t.c_str());
            evLog(("ANN:"+t.substring(0,40)).c_str());
        } else ok = false;
    }
    else { ok=false; Serial.printf("[CTRL] Unknown: '%s'\n",cmd.c_str()); }

    server.send(200,"application/json",ok?"{\"ok\":true}":"{\"ok\":false}");
}

// ═══════════════════════════════════════════════════════
//  SETUP — exact init order from official examples
// ═══════════════════════════════════════════════════════
void setup() {
    Serial.begin(115200);
    delay(400);
    Serial.println("\n══════ SENTINEL v11.0 ══════");
    Serial.println("Patterns from DFR1154_Examples-master.zip");

    // Semaphores & queues
    mx_prev = xSemaphoreCreateMutex();
    mx_sd   = xSemaphoreCreateMutex();
    mx_ev   = xSemaphoreCreateMutex();
    g_spkQ  = xQueueCreate(6, sizeof(SpkJob));

    // Battery (before ADC contention)
    if (BATTERY_WIRED) {
        analogSetAttenuation(ADC_11db);
        pinMode(BAT_PIN, INPUT);
        readBattery();
        Serial.printf("[BAT] %.2fV %d%%\n", g_vbat, g_batPct);
    }

    // ── 1. CAMERA — must be before ALS (from 5_1.ino comment) ───
    Serial.print("[CAM] ");
    if (!initCamera()) {
        Serial.println("FAILED — halting");
        pinMode(PIN_LED, OUTPUT);
        while (true) {
            digitalWrite(PIN_LED, HIGH); delay(200);
            digitalWrite(PIN_LED, LOW);  delay(200);
        }
    }
    Serial.println("OK");

    // ── 2. Status LED (from 6_9.ino: pinMode(3,OUTPUT)) ─────────
    pinMode(PIN_LED, OUTPUT);
    digitalWrite(PIN_LED, LOW);

    // ── 3. IR LED — from app_httpd.cpp setupLedFlash() ──────────
    //    ledcAttach(pin, 5000, 8)  then ledcWrite to control
    irSetup();   // ledcAttach(47, 5000, 8); ledcWrite(47, 0)

    // ── 4. ALS — from 5_1.ino: after camera (mandatory) ─────────
    initALS();

    // ── 5. I2S mic (from 5_2.ino: i2s first → I2S_NUM_0) ────────
    initMic();

    // ── 6. I2S speaker (from 5_2.ino: i2s1 second → I2S_NUM_1) ──
    initSpeaker();

    // ── 7. SD ─────────────────────────────────────────────────────
    if (SD.begin(SD_CS)) {
        g_sdOK = true;
        Serial.printf("[SD]  OK %.2fGB free\n",
            (float)(SD.totalBytes()-SD.usedBytes())/1073741824.0f);
    } else Serial.println("[SD]  No card");

    // ── 8. WiFi ───────────────────────────────────────────────────
    WiFi.mode(WIFI_STA); WiFi.setSleep(false);
    WiFi.setTxPower(WIFI_POWER_19_5dBm);
    WiFi.begin(WIFI_SSID, WIFI_PASS);
    Serial.print("[WiFi] ");
    for (uint8_t t=0; WiFi.status()!=WL_CONNECTED; t++) {
        delay(500); Serial.print('.');
        if (t>40) { Serial.println("FAILED"); while(1){}; }
    }
    Serial.printf("\n[WiFi] IP: %s  RSSI: %d\n",
        WiFi.localIP().toString().c_str(), WiFi.RSSI());
    digitalWrite(PIN_LED, HIGH);

    configTime(TZ_OFFSET_SEC, 0, "pool.ntp.org", "time.nist.gov");

    // ── 9. HTTP ───────────────────────────────────────────────────
    server.on("/",         HTTP_GET,     handleRoot);
    server.on("/stream",   HTTP_GET,     handleStream);
    server.on("/snapshot", HTTP_GET,     handleSnapshot);
    server.on("/data",     HTTP_GET,     handleData);
    server.on("/control",  HTTP_GET,     handleControl);
    server.on("/control",  HTTP_POST,    handleControl);
    server.on("/stream",   HTTP_OPTIONS, handleOptions);
    server.on("/data",     HTTP_OPTIONS, handleOptions);
    server.on("/control",  HTTP_OPTIONS, handleOptions);
    server.on("/snapshot", HTTP_OPTIONS, handleOptions);
    server.begin();
    Serial.println("[HTTP] Port 80 ready");

    // ── 10. FreeRTOS tasks ────────────────────────────────────────
    xTaskCreatePinnedToCore(streamTask,"stream", 8192,nullptr,5,nullptr,0);
    xTaskCreatePinnedToCore(sensorTask,"sensor", 6144,nullptr,3,nullptr,0);
    xTaskCreatePinnedToCore(spkTask,   "speaker",6144,nullptr,2,nullptr,1);

    if (g_sdOK) startAVI();
    qSpk(BEEP_BOOT);
    evLog("SENTINEL v1.0 online");
    Serial.printf("Open dashboard → set IP: %s\n",
        WiFi.localIP().toString().c_str());
    Serial.println("════════════════════════════════");
}

// ═══════════════════════════════════════════════════════
//  LOOP — Core 1, never blocks > 2ms
// ═══════════════════════════════════════════════════════
void loop() {
    server.handleClient();

    // Status LED: solid=recording, fast=streaming, slow=idle
    static uint32_t lb=0; static bool ls=false;
    uint32_t now=millis();
    uint32_t rate=g_recording?300:(g_strOn?120:1200);
    if(now-lb>rate){lb=now;ls=!ls;
        digitalWrite(PIN_LED,g_recording?HIGH:(ls?HIGH:LOW));}

    // AVI watchdog
    static uint32_t wdT=0;
    if(g_sdOK&&!g_recording&&now-wdT>12000){
        wdT=now; startAVI(); evLog("WD:AVI restart");
    }

    delay(2);
}
