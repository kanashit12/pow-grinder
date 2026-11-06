#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <pthread.h>
#include <openssl/sha.h>
static char prefix[256]; static int plen;
static volatile int found_count = 0; static int want = 2;
static pthread_mutex_t lk = PTHREAD_MUTEX_INITIALIZER;
static void* worker(void* arg){
    long tid = (long)arg; uint64_t n = (uint64_t)tid; const uint64_t step = 4;
    char buf[320]; unsigned char d[32];
    uint64_t local = 0;
    while(found_count < want){
        int len = plen + snprintf(buf+plen, sizeof(buf)-plen, "%llu", (unsigned long long)n);
        memcpy(buf, prefix, plen);
        SHA256((unsigned char*)buf, len, d);
        if(d[0]==0 && d[1]==0 && d[2]==0 && (d[3]>>4)==0){
            pthread_mutex_lock(&lk);
            if(found_count < want){
                printf("FOUND work=%llu hex=", (unsigned long long)n);
                for(int i=0;i<32;i++) printf("%02x", d[i]);
                printf("\n"); fflush(stdout);
                found_count++;
            }
            pthread_mutex_unlock(&lk);
        }
        n += step; local++;
        if(local == 20000000){ local = 0; if(found_count >= want) break; }
    }
    return NULL;
}
int main(int argc, char** argv){
    if(argc < 3){ fprintf(stderr, "usage: grindc <wallet_lower> <puzzleId> [want]\n"); return 1; }
    if(argc > 3) want = atoi(argv[3]);
    plen = snprintf(prefix, sizeof(prefix), "tampesta-work|%s|%s|", argv[1], argv[2]);
    pthread_t th[4];
    for(long i=0;i<4;i++) pthread_create(&th[i], NULL, worker, (void*)i);
    for(int i=0;i<4;i++) pthread_join(th[i], NULL);
    return 0;
}
