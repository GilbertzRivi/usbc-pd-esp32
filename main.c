#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/queue.h"
#include "freertos/portmacro.h"
#include "esp_log.h"
#include "driver/gpio.h"
#include "esp_timer.h"
#include <esp_adc/adc_oneshot.h>
#include <string.h>
#include <inttypes.h>
#include <esp_check.h>
#include "math.h"
#include "soc/gpio_sig_map.h"
#include "soc/io_mux_reg.h"
#include "soc/gpio_reg.h"
#include "soc/gpio_struct.h"
#include "driver/gptimer.h"
#include "esp_system.h"
#include "driver/i2s_std.h"
#include "driver/ledc.h"
#include "esp32/rom/crc.h"

#define TX_PIN                  47
#define NO_DVC_V                2
#define BUCKCCPIN               4
#define VBUS_EN_PIN             5

#define PREAMBLE                0b01010101010101010101010101010101
#define SYNC1                   0b11000
#define SYNC2                   0b10001
#define SYNC3                   0b00110
#define RST1                    0b00111
#define RST2                    0b11001
#define EOP                     0b01101


#define ADC_CHANNEL        ADC_CHANNEL_2

#define PWM_GPIO           GPIO_NUM_4      // GPIO for PWM output
#define PWM_FREQUENCY      4000            // PWM frequency in Hz
#define PWM_RESOLUTION     LEDC_TIMER_14_BIT  // 14-bit resolution for duty cycle
#define PWM_MAX_DUTY       ((1 << 14) - 1)    // Maximum duty cycle for 14-bit resolution
#define PWM_MIN_DUTY       0

#define TARGET_VOLTAGE     5.0f            // Target voltage in volts
#define ADC_MAX_VOLTAGE    24.0f           // Maximum voltage at the input of the divider

#define ADC_SAMPLES             64         

#define BYTE_TO_BINARY_PATTERN "%c%c%c%c%c%c%c%c"
#define BYTE_TO_BINARY(byte)  \
  ((byte) & 0x80 ? '1' : '0'), \
  ((byte) & 0x40 ? '1' : '0'), \
  ((byte) & 0x20 ? '1' : '0'), \
  ((byte) & 0x10 ? '1' : '0'), \
  ((byte) & 0x08 ? '1' : '0'), \
  ((byte) & 0x04 ? '1' : '0'), \
  ((byte) & 0x02 ? '1' : '0'), \
  ((byte) & 0x01 ? '1' : '0') 


// Voltage divider constants
#define R1 47000.0f  // 47k ohm
#define R2 6800.0f   // 6.8k ohm

typedef struct {
    uint8_t V;
    uint8_t A;
} src_cap;

typedef struct {
    uint32_t *array;
    size_t size;
} ptr_and_size;

typedef struct {
    uint8_t sop[4];
    uint16_t header;
    uint32_t data[7];
    size_t data_size;
    uint32_t crc; 
    uint8_t eop;
    uint8_t *bmc_encoded;
    size_t bmc_size;
    uint8_t *b4b5_encoded;
    size_t b4b5_size;
    bool *bit_tape;
    size_t tape_size;
    uint32_t *wide_data;
    size_t wide_size;
} PD_Packet;

volatile PD_Packet PD_data = {
    .sop = {0,0,0,0}, .header = 0, .crc = 0, .data = {0,0,0,0,0,0,0}, .data_size = 0, .eop = EOP, .bmc_size = 0, .b4b5_size = 0, .tape_size = 0, .wide_size = 0,
};

#define BMC_MAX_SIZE                256
#define B4B5_MAX_SIZE               256
#define WIDE_MAX_SIZE               256
#define TAPE_MAX_SIZE               2048

#define MAX5V                   (src_cap){.V = 5, .A = 3}
#define MAX9V                   (src_cap){.V = 9, .A = 3}
#define MAX12V                   (src_cap){.V = 12, .A = 3}
#define MAX15V                   (src_cap){.V = 15, .A = 3}
#define MAX20V                   (src_cap){.V = 20, .A = 5}

portMUX_TYPE my_spinlock = portMUX_INITIALIZER_UNLOCKED;
static const char *TAG = "EPS32-USBC-PD";

i2s_chan_handle_t i2s_channel;

static uint8_t encoding_table[16] = {
    0b11110, // 0000  0
    0b01001, // 0001  1
    0b10100, // 0010  2
    0b10101, // 0011  3
    0b01010, // 0100  4
    0b01011, // 0101  5
    0b01110, // 0110  6 
    0b01111, // 0111  7
    0b10010, // 1000  8
    0b10011, // 1001  9
    0b10110, // 1010  A
    0b10111, // 1011  B
    0b11010, // 1100  C
    0b11011, // 1101  D
    0b11100, // 1110  E
    0b11101, // 1111  F
};

adc_oneshot_unit_handle_t adc1_handle;
adc_oneshot_unit_handle_t adc2_handle;
adc_oneshot_unit_init_cfg_t init_config1 = {
    .unit_id = ADC_UNIT_1,
};
adc_oneshot_unit_init_cfg_t init_config2 = {
    .unit_id = ADC_UNIT_2,
};
adc_oneshot_chan_cfg_t config = {
    .bitwidth = ADC_BITWIDTH_DEFAULT,
    .atten = ADC_ATTEN_DB_12,
};

int adc_raw[2][10];
int adc2_raw[2][10];
float voltage;
volatile uint8_t msg_id = 0;
uint32_t crc;

#define CRC32_INITIAL 0xFFFFFFFF

static const uint32_t crc32_tab[] = {
	0x00000000, 0x77073096, 0xee0e612c, 0x990951ba, 0x076dc419, 0x706af48f,
	0xe963a535, 0x9e6495a3, 0x0edb8832, 0x79dcb8a4, 0xe0d5e91e, 0x97d2d988,
	0x09b64c2b, 0x7eb17cbd, 0xe7b82d07, 0x90bf1d91, 0x1db71064, 0x6ab020f2,
	0xf3b97148, 0x84be41de, 0x1adad47d, 0x6ddde4eb, 0xf4d4b551, 0x83d385c7,
	0x136c9856, 0x646ba8c0, 0xfd62f97a, 0x8a65c9ec, 0x14015c4f, 0x63066cd9,
	0xfa0f3d63, 0x8d080df5, 0x3b6e20c8, 0x4c69105e, 0xd56041e4, 0xa2677172,
	0x3c03e4d1, 0x4b04d447, 0xd20d85fd, 0xa50ab56b, 0x35b5a8fa, 0x42b2986c,
	0xdbbbc9d6, 0xacbcf940, 0x32d86ce3, 0x45df5c75, 0xdcd60dcf, 0xabd13d59,
	0x26d930ac, 0x51de003a, 0xc8d75180, 0xbfd06116, 0x21b4f4b5, 0x56b3c423,
	0xcfba9599, 0xb8bda50f, 0x2802b89e, 0x5f058808, 0xc60cd9b2, 0xb10be924,
	0x2f6f7c87, 0x58684c11, 0xc1611dab, 0xb6662d3d, 0x76dc4190, 0x01db7106,
	0x98d220bc, 0xefd5102a, 0x71b18589, 0x06b6b51f, 0x9fbfe4a5, 0xe8b8d433,
	0x7807c9a2, 0x0f00f934, 0x9609a88e, 0xe10e9818, 0x7f6a0dbb, 0x086d3d2d,
	0x91646c97, 0xe6635c01, 0x6b6b51f4, 0x1c6c6162, 0x856530d8, 0xf262004e,
	0x6c0695ed, 0x1b01a57b, 0x8208f4c1, 0xf50fc457, 0x65b0d9c6, 0x12b7e950,
	0x8bbeb8ea, 0xfcb9887c, 0x62dd1ddf, 0x15da2d49, 0x8cd37cf3, 0xfbd44c65,
	0x4db26158, 0x3ab551ce, 0xa3bc0074, 0xd4bb30e2, 0x4adfa541, 0x3dd895d7,
	0xa4d1c46d, 0xd3d6f4fb, 0x4369e96a, 0x346ed9fc, 0xad678846, 0xda60b8d0,
	0x44042d73, 0x33031de5, 0xaa0a4c5f, 0xdd0d7cc9, 0x5005713c, 0x270241aa,
	0xbe0b1010, 0xc90c2086, 0x5768b525, 0x206f85b3, 0xb966d409, 0xce61e49f,
	0x5edef90e, 0x29d9c998, 0xb0d09822, 0xc7d7a8b4, 0x59b33d17, 0x2eb40d81,
	0xb7bd5c3b, 0xc0ba6cad, 0xedb88320, 0x9abfb3b6, 0x03b6e20c, 0x74b1d29a,
	0xead54739, 0x9dd277af, 0x04db2615, 0x73dc1683, 0xe3630b12, 0x94643b84,
	0x0d6d6a3e, 0x7a6a5aa8, 0xe40ecf0b, 0x9309ff9d, 0x0a00ae27, 0x7d079eb1,
	0xf00f9344, 0x8708a3d2, 0x1e01f268, 0x6906c2fe, 0xf762575d, 0x806567cb,
	0x196c3671, 0x6e6b06e7, 0xfed41b76, 0x89d32be0, 0x10da7a5a, 0x67dd4acc,
	0xf9b9df6f, 0x8ebeeff9, 0x17b7be43, 0x60b08ed5, 0xd6d6a3e8, 0xa1d1937e,
	0x38d8c2c4, 0x4fdff252, 0xd1bb67f1, 0xa6bc5767, 0x3fb506dd, 0x48b2364b,
	0xd80d2bda, 0xaf0a1b4c, 0x36034af6, 0x41047a60, 0xdf60efc3, 0xa867df55,
	0x316e8eef, 0x4669be79, 0xcb61b38c, 0xbc66831a, 0x256fd2a0, 0x5268e236,
	0xcc0c7795, 0xbb0b4703, 0x220216b9, 0x5505262f, 0xc5ba3bbe, 0xb2bd0b28,
	0x2bb45a92, 0x5cb36a04, 0xc2d7ffa7, 0xb5d0cf31, 0x2cd99e8b, 0x5bdeae1d,
	0x9b64c2b0, 0xec63f226, 0x756aa39c, 0x026d930a, 0x9c0906a9, 0xeb0e363f,
	0x72076785, 0x05005713, 0x95bf4a82, 0xe2b87a14, 0x7bb12bae, 0x0cb61b38,
	0x92d28e9b, 0xe5d5be0d, 0x7cdcefb7, 0x0bdbdf21, 0x86d3d2d4, 0xf1d4e242,
	0x68ddb3f8, 0x1fda836e, 0x81be16cd, 0xf6b9265b, 0x6fb077e1, 0x18b74777,
	0x88085ae6, 0xff0f6a70, 0x66063bca, 0x11010b5c, 0x8f659eff, 0xf862ae69,
	0x616bffd3, 0x166ccf45, 0xa00ae278, 0xd70dd2ee, 0x4e048354, 0x3903b3c2,
	0xa7672661, 0xd06016f7, 0x4969474d, 0x3e6e77db, 0xaed16a4a, 0xd9d65adc,
	0x40df0b66, 0x37d83bf0, 0xa9bcae53, 0xdebb9ec5, 0x47b2cf7f, 0x30b5ffe9,
	0xbdbdf21c, 0xcabac28a, 0x53b39330, 0x24b4a3a6, 0xbad03605, 0xcdd70693,
	0x54de5729, 0x23d967bf, 0xb3667a2e, 0xc4614ab8, 0x5d681b02, 0x2a6f2b94,
	0xb40bbe37, 0xc30c8ea1, 0x5a05df1b, 0x2d02ef8d
};

static uint32_t crc32_hash(uint32_t crc, const void *buf, int size){
	const uint8_t *p;
	p = buf;
	while (size--) {
		crc ^= *p++;
		crc = crc32_tab[crc & 0xFF] ^ (crc >> 8);
	}
	return crc;
}

void crc32_ctx_init(uint32_t *crc){
	*crc = CRC32_INITIAL;
}

void crc32_ctx_hash32(uint32_t *crc, uint32_t val){
	*crc = crc32_hash(*crc, &val, sizeof(val));
}

void crc32_ctx_hash16(uint32_t *crc, uint16_t val){
	*crc = crc32_hash(*crc, &val, sizeof(val));
}

void crc32_ctx_hash8(uint32_t *crc, uint8_t val){
	*crc = crc32_hash(*crc, &val, sizeof(val));
}

uint32_t crc32_ctx_result(uint32_t *crc){
	return *crc ^ 0xFFFFFFFF;
}

static uint32_t crc_;
void crc32_init(void){
	crc32_ctx_init(&crc_);
}

void crc32_hash32(uint32_t val){
	crc32_ctx_hash32(&crc_, val);
}

void crc32_hash16(uint16_t val){
	crc32_ctx_hash16(&crc_, val);
}

uint32_t crc32_result(void){
	return crc32_ctx_result(&crc_);
}

void uint_to_binary_string(uint64_t value, char *buffer, size_t buffer_size, size_t bit_count) {
    if (buffer_size < bit_count + 1) {
        return;
    }

    buffer[bit_count] = '\0';
    for (int i = bit_count - 1; i >= 0; i--) {
        buffer[i] = (value & 1) ? '1' : '0';
        value >>= 1;
    }
}

void uint8_to_binary_string(uint8_t value, char *buffer, size_t buffer_size) {
    uint_to_binary_string(value, buffer, buffer_size, 8);
}

void uint16_to_binary_string(uint16_t value, char *buffer, size_t buffer_size) {
    uint_to_binary_string(value, buffer, buffer_size, 16);
}

void uint32_to_binary_string(uint32_t value, char *buffer, size_t buffer_size) {
    uint_to_binary_string(value, buffer, buffer_size, 32);
}

void uint64_to_binary_string(uint64_t value, char *buffer, size_t buffer_size) {
    uint_to_binary_string(value, buffer, buffer_size, 64);
}


size_t get_packet_binary_length(){
    return ((PD_data.data_size * 32) + 16 + 32); // data packets + header + crc 
}

void encode_4b5b() {
    PD_data.b4b5_size = ((((get_packet_binary_length() * 5) / 4) + (64 + 20 + 5)) / 8) + 1;
    PD_data.tape_size = ((get_packet_binary_length() * 5) / 4) + (64 + 20 + 5);
    memset(PD_data.b4b5_encoded, 0, PD_data.b4b5_size * sizeof(uint8_t));
    memset(PD_data.bit_tape, 0, PD_data.tape_size * sizeof(bool));
    size_t current_bit = 0;
    // Encoded with LSB first
    // Preamble
    for(int i = 0; i < 64; i++){
        PD_data.bit_tape[current_bit] = (i % 2);
        current_bit ++;
    }
    // SOP
    for(int i = 0; i < 20; i++){
        PD_data.bit_tape[current_bit] = PD_data.sop[i/5] >> (i % 5) & 1;
        current_bit ++;
    }
    // Header
    for(int i = 0; i < 4; i++){
        for (int j = 0; j < 5; j++){
            PD_data.bit_tape[current_bit] = (encoding_table[PD_data.header >> i*4 & 15] >> j) & 1;
            current_bit ++;
        }
    }
    // Data
    for(int i = 0; i < PD_data.data_size; i++){
        for(int j = 0; j < 8; j++){
            for (int l = 0; l < 5; l++){
                PD_data.bit_tape[current_bit] = (encoding_table[PD_data.data[i] >> j*4 & 15] >> l) & 1;
                current_bit ++;
            }
        }
    }
    // CRC
    for(int i = 0; i < 8; i++){
        for (int j = 0; j < 5; j++){
            PD_data.bit_tape[current_bit] = (encoding_table[PD_data.crc >> i*4 & 15] >> j) & 1;
            current_bit ++;
        }
    }
    for (int i = 0; i < 5; i++){
        PD_data.bit_tape[current_bit] = EOP >> i & 1;
        current_bit ++;
    }
    // Make it array of uint 8
    uint8_t byte = 0;
    current_bit = 0;
    while(current_bit < PD_data.tape_size){
        byte |= (PD_data.bit_tape[current_bit] & 1) << (7 - (current_bit % 8));
        if(current_bit%8==7){
            PD_data.b4b5_encoded[current_bit/8] = byte;
            byte = 0;
        }
        current_bit ++;
    }
    PD_data.b4b5_encoded[current_bit/8] = byte;
}


void static get_payload(src_cap *cap, size_t cap_size){
    uint32_t data;
    for (int i = 0; i < cap_size; i++){
        data = 0;
        data |= 0b00 << 31; // power supply type 0b00 for fixed psu
        data |= 0b0 << 29; // dual role power, 0b0 for no
        data |= 0b0 << 28; // suspend support, 0b0 for no
        data |= 0b1 << 27; // unconstrained power, 0b1 for yes
        data |= 0b1 << 26; // usb communication cappable, 0b1 for yes
        data |= 0b1 << 25; // usb data dual role cappable, 0b1 for yes
        data |= 0b000 << 22; // reserved
        data |= 0b00 << 20; // peak current cap, 0b00 for no
        data |= (cap[i].V * 20) << 10; // V to 50mV steps
        data |= (cap[i].A * 100); // A to 10mA steps
        PD_data.data[i] = data;
        PD_data.data_size ++;
    }
}


uint16_t static get_header(bool extended){
    uint16_t header = 0;
    if (extended){
        header |= 0b1 << 15; // Set 1 if the message is extended
    }
    else {
        header |= 0b0 << 15;
    }
    if (!extended){
        if (PD_data.data_size > 7){
            return 0;
        }
        header |= (PD_data.data_size & 0b111) << 12; // Set the number of data objects
    }
    header |= (msg_id & 0b111) << 9; // Set the msg ID
    header |= 0b1 << 8; // Set power role
    header |= 0b10 << 6; // Set specification revision 0b10 for revision 3.0
    header |= 0b1 << 5; // Set port data role
    header |= 0b00001; // Set message type, 0b00001 for source_capabilities
    return header;
}

uint32_t get_crc(){
    crc32_init();
    crc32_hash16(PD_data.header);
    for(int i = 0; i < PD_data.data_size; i++){
        crc32_hash32(PD_data.data[i]);
    }
    return crc32_result();
}

void get_src_cap_packet(){

    PD_data.sop[0] = SYNC1;
    PD_data.sop[1] = SYNC1;
    PD_data.sop[2] = SYNC1;
    PD_data.sop[3] = SYNC2;
    src_cap caps[5] = {
        { .V = 5, .A = 3},
        { .V = 9, .A = 3},
        { .V = 12, .A = 3},
        { .V = 15, .A = 3},
        { .V = 20, .A = 5},
    };
    get_payload(caps, 5);
    PD_data.header = get_header(false);
    PD_data.crc = get_crc();
}


void bmc_encoding() {
    PD_data.bmc_size = PD_data.b4b5_size * 2;
    memset(PD_data.bmc_encoded, 0, PD_data.bmc_size * sizeof(uint8_t));

    uint8_t previousState = 1; // Initial state is 1
    size_t outIndex = 0; // Index for the output array
    uint8_t bitBuffer = 0; // Buffer to accumulate bits before writing to output
    int bitCount = 0; // Count of bits in bitBuffer

    // Process each byte in the input array
    for (size_t i = 0; i < PD_data.b4b5_size; i++) {
        uint8_t byte = PD_data.b4b5_encoded[i];

        // Process each bit in the byte
        for (int j = 0; j < 8; j++) {
            uint8_t bit = (byte >> (7 - j)) & 1; // Extract the j-th bit from the byte

            if (bit == 1) {
                // Encode 1 as !previousState followed by previousState
                bitBuffer = (bitBuffer << 1) | (!previousState); // !previousState
                bitCount++;
                bitBuffer = (bitBuffer << 1) | previousState;   // previousState
                bitCount++;
            } else {
                // Encode 0 as !previousState followed by !previousState
                bitBuffer = (bitBuffer << 1) | (!previousState); // !previousState
                bitCount++;
                bitBuffer = (bitBuffer << 1) | (!previousState); // !previousState
                bitCount++;
                previousState = !previousState;
            }

            if (bitCount == 8) {
                PD_data.bmc_encoded[outIndex++] = bitBuffer;
                bitBuffer = 0;
                bitCount = 0;
            }
        }
    }
}


void expand_bits_to_uint32() {
    PD_data.wide_size = PD_data.bmc_size;
    for (size_t i = 0; i < PD_data.bmc_size; ++i) {
        uint8_t value = PD_data.bmc_encoded[i];
        uint32_t expanded = 0;

        for (int bit = 0; bit < 8; ++bit) {
            // Extract the bit (0 or 1)
            uint8_t bitValue = (value >> (7 - bit)) & 1;

            // Expand the bit to 4 bits (0000 or 1111)
            uint32_t expandedBit = bitValue ? 0xF : 0x0;

            // Shift the expanded bits into their correct position in the output
            expanded |= (expandedBit << ((7 - bit) * 4));
        }

        // Store the expanded value in the temporary array
        PD_data.wide_data[i] = expanded;
    }

}


void invert_bits() {
    for (size_t i = 0; i < PD_data.wide_size; ++i) {
        PD_data.wide_data[i] = ~PD_data.wide_data[i];
    }
}

static void IRAM_ATTR i2s_tx(void *params) {
    size_t bytes_written;
    esp_err_t err = i2s_channel_write(i2s_channel, PD_data.wide_data, PD_data.wide_size * sizeof(uint32_t), &bytes_written, portMAX_DELAY);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Write failed: %s", esp_err_to_name(err));
    }
    else{
        ESP_LOGI(TAG, "Write successfull");
    }
    vTaskDelete(NULL);
}


void print_uint32_array_as_binary(uint32_t* array, size_t size) {
    for (size_t i = 0; i < size; i++) {
        uint32_t value = array[i];
        // Print each bit of the 32-bit integer
        for (int j = 31; j >= 0; j--) {
            // Check if the j-th bit is set and print '1' or '0'
            printf("%d", (value & (1 << j)) ? 1 : 0);
        }
    }
    printf("\n");
}


void print_uint8_array_as_binary(uint8_t* array, size_t size) {
    for (size_t i = 0; i < size; i++) {
        uint8_t value = array[i];
        // Print each bit of the 32-bit integer
        for (int j = 7; j >= 0; j--) {
            // Check if the j-th bit is set and print '1' or '0'
            printf("%d", (value & (1 << j)) ? 1 : 0);
        }
    }
    printf("\n");
}

static void encode_packet(void *arg) {

    get_src_cap_packet();
    encode_4b5b();
    bmc_encoding();
    expand_bits_to_uint32();
    invert_bits();

    print_uint8_array_as_binary(PD_data.b4b5_encoded, PD_data.b4b5_size);

    xTaskCreatePinnedToCore(i2s_tx, "i2s_tx", 4096, NULL, configMAX_PRIORITIES-1, NULL, 1);
    vTaskDelay(pdMS_TO_TICKS(500));

    // // vTaskDelay(pdMS_TO_TICKS(100));
    // // xTaskCreate(rmt_receive_task, "rmt_receive_task", 4096, NULL, 5, NULL);
    vTaskDelete(NULL);
}


static void monitor_adc_task(void *arg){
    while (1)
    {
        ESP_ERROR_CHECK(adc_oneshot_read(adc1_handle, ADC_CHANNEL_0, &adc_raw[0][0]));
        voltage = adc_raw[0][0] * (3.3 / 4096.0); 

        // ESP_LOGI(TAG, "ADC Reading: %d, Voltage: %.2fV", adc_raw[0][0], voltage);

        if (voltage < NO_DVC_V)
        {
            ESP_LOGI(TAG, "Voltage drop detected, starting transmiter...");
            vTaskDelay(pdMS_TO_TICKS(500));
            xTaskCreate(encode_packet, "encode_packet", 4096, NULL, 5, NULL);
            vTaskDelete(NULL);
        }

        vTaskDelay(pdMS_TO_TICKS(100));
    }
}

float read_adc_voltage(adc_oneshot_unit_handle_t adc_handle) {
    uint32_t sum = 0;
    for (int i = 0; i < ADC_SAMPLES; i++) {
        int raw_value;
        adc_oneshot_read(adc_handle, ADC_CHANNEL_1, &raw_value);
        sum += raw_value;
    }
    float average = (float)sum / ADC_SAMPLES;
    // Convert to voltage (assuming a 12-bit ADC and a reference voltage of 3.3V)
    float voltage = (average / 4095.0) * 3.3;
    float input_voltage = voltage * ((R1 + R2) / R2);
    return input_voltage;
}


bool setup(void){
    ESP_ERROR_CHECK(adc_oneshot_new_unit(&init_config1, &adc1_handle));
    ESP_ERROR_CHECK(adc_oneshot_config_channel(adc1_handle, ADC_CHANNEL_0, &config));
    ESP_ERROR_CHECK(adc_oneshot_new_unit(&init_config2, &adc2_handle));
    ESP_ERROR_CHECK(adc_oneshot_config_channel(adc2_handle, ADC_CHANNEL_1, &config));

    gpio_pulldown_en(47);
    i2s_chan_config_t chan_cfg = I2S_CHANNEL_DEFAULT_CONFIG(I2S_NUM_AUTO, I2S_ROLE_MASTER);
    i2s_new_channel(&chan_cfg, &i2s_channel, NULL);
    i2s_std_config_t std_cfg = {
        .clk_cfg = {
            .sample_rate_hz = 40000,
            .clk_src = I2S_CLK_SRC_DEFAULT,
            .mclk_multiple = I2S_MCLK_MULTIPLE_1024,
        },
        .slot_cfg = {
            .data_bit_width = I2S_DATA_BIT_WIDTH_32BIT,
            .slot_bit_width = I2S_SLOT_BIT_WIDTH_8BIT,
            .slot_mode = I2S_SLOT_MODE_STEREO,
            .slot_mask = I2S_STD_SLOT_BOTH,
            .ws_width = I2S_DATA_BIT_WIDTH_8BIT,
            .ws_pol = 0,
            .bit_shift = 0, 
            .left_align = 0,
            .big_endian = 0,
            .bit_order_lsb = 0
        },
        .gpio_cfg = {
            .mclk = I2S_GPIO_UNUSED,
            .bclk = I2S_GPIO_UNUSED,
            .ws = I2S_GPIO_UNUSED,
            .dout = 47,
            .din = I2S_GPIO_UNUSED,
            .invert_flags = {
                .mclk_inv = false,
                .bclk_inv = false,
                .ws_inv = false,
            },
        },
    };
    i2s_channel_init_std_mode(i2s_channel, &std_cfg);
    i2s_channel_enable(i2s_channel);
    gpio_set_direction(BUCKCCPIN, GPIO_MODE_OUTPUT);
    gpio_set_direction(VBUS_EN_PIN, GPIO_MODE_OUTPUT);

    ledc_timer_config_t ledc_timer = {
        .speed_mode       = LEDC_LOW_SPEED_MODE,
        .duty_resolution  = LEDC_TIMER_14_BIT,
        .timer_num        = LEDC_TIMER_0,
        .freq_hz          = 4000,
        .clk_cfg          = LEDC_AUTO_CLK
    };
    ESP_ERROR_CHECK(ledc_timer_config(&ledc_timer));

    ledc_channel_config_t ledc_channel = {
        .speed_mode     = LEDC_LOW_SPEED_MODE,
        .channel        = LEDC_CHANNEL_0,
        .timer_sel      = LEDC_TIMER_0,
        .intr_type      = LEDC_INTR_DISABLE,
        .gpio_num       = 4,
        .duty           = 0,
        .hpoint         = 0
    };
    ESP_ERROR_CHECK(ledc_channel_config(&ledc_channel));

    PD_data.b4b5_encoded = malloc(B4B5_MAX_SIZE * sizeof(uint8_t));
    if (PD_data.b4b5_encoded == NULL) {
        ESP_LOGE(TAG, "Memory allocation failed for b4b5_encoded");
        return false;
    }
    memset(PD_data.b4b5_encoded, 0, B4B5_MAX_SIZE * sizeof(uint8_t));
    PD_data.bit_tape = malloc(TAPE_MAX_SIZE * sizeof(bool));
    if (PD_data.b4b5_encoded == NULL) {
        ESP_LOGE(TAG, "Memory allocation failed for bit_tape");
        return false;
    }
    memset(PD_data.bit_tape, 0, TAPE_MAX_SIZE * sizeof(bool));
    PD_data.bmc_encoded = malloc(BMC_MAX_SIZE * sizeof(uint8_t));
    if (PD_data.b4b5_encoded == NULL) {
        ESP_LOGE(TAG, "Memory allocation failed for bmc_encoded");
        return false;
    }
    memset(PD_data.bmc_encoded, 0, BMC_MAX_SIZE * sizeof(uint8_t));
    PD_data.wide_data = malloc(WIDE_MAX_SIZE * sizeof(uint32_t));
    if (PD_data.wide_data == NULL) {
        ESP_LOGE(TAG, "Memory allocation failed for wide_data");
        return false;
    }
    memset(PD_data.wide_data, 0, WIDE_MAX_SIZE * sizeof(uint32_t));
    return true;
}


void control_task(void *arg) {
    int duty_cycle = 4000;

    // ADC handle passed as argument
    adc_oneshot_unit_handle_t adc2_handle = (adc_oneshot_unit_handle_t)arg;

    while (1) {
        // Read the average voltage
        float voltage = read_adc_voltage(adc2_handle);
        if (voltage - 0.1 < TARGET_VOLTAGE && voltage + 0.1 > TARGET_VOLTAGE){
            gpio_set_level(VBUS_EN_PIN, 1);
        }
        else{
            gpio_set_level(VBUS_EN_PIN, 0);
        }

        // Calculate the error
        float error = voltage - TARGET_VOLTAGE;
        
        // Proportional control to adjust PWM duty cycle
        int adjustment = (int)(error * 25);
        duty_cycle += adjustment;
        
        // Limit the duty cycle within valid range
        if (duty_cycle > PWM_MAX_DUTY) duty_cycle = PWM_MAX_DUTY;
        if (duty_cycle < PWM_MIN_DUTY) duty_cycle = PWM_MIN_DUTY;

        // Set the new duty cycle
        ledc_set_duty(LEDC_LOW_SPEED_MODE, LEDC_CHANNEL_0, duty_cycle);
        ledc_update_duty(LEDC_LOW_SPEED_MODE, LEDC_CHANNEL_0);

        // Delay for stability
        vTaskDelay(pdMS_TO_TICKS(100));
    }
}

void app_main(void){

    if(!setup()){
        ESP_LOGE(TAG, "ERROR ABORTING");
        return;
    }

    xTaskCreate(control_task, "control_task", 4096, (void*)adc2_handle, 5, NULL);

    vTaskDelay(pdMS_TO_TICKS(500));
    
    xTaskCreate(monitor_adc_task, "monitor_adc_task", 4096, NULL, 5, NULL);
}