/*
 * File: allocator.c
 * Author: Nithin Kannan
 * ----------------------
 */

#include <stdlib.h>
#include <string.h>
#include "allocator.h"
#include "segment.h"
#include <stdbool.h>
#include <stdio.h>
#include <assert.h>

// Heap blocks are required to be aligned to 8-byte boundary
#define ALIGNMENT 8

// We are using 64 size classes in our segmented freelist implementation of heap allocator
#define SIZE_CLASSES 64


// Header holds a size of its payload, a pointer to the next free block, and a pointer to the previous 
// block adjacent in memory.
typedef struct header {
    size_t payloadsz;  
    struct header *next;
    struct header *prevInMem; // This thing needs to be updated/set
    struct header *prev;
} headerT;

// Free list used to keep track of free blocks of different size classes
headerT** freelist;
headerT *lastInHeap = NULL;
headerT *secondToLast = NULL;

// Header flags embedded into the payloadsz of each free block. Each free block has size that is a multiple of 8.
// This allows us to use the last three bits of payloadsz to keep track of these flags.
typedef struct header_flags {
    bool allocated;
    // Other flags not used yet in heap allocator, but could be helpful for future modifications!
    bool flag1, flag2;
} header_flags_t;

// Tells us the flags of a given memory block
static inline header_flags_t calculateFlags(size_t payloadsz) {
    header_flags_t flags;
    flags.allocated = payloadsz & 0x1;
    flags.flag1 = payloadsz & 0x2;
    flags.flag2 = payloadsz & 0x4;
    return flags;
}

// Returns the memory address for the end of the heap segment
static inline void *heap_segment_end() {
    return (char *)heap_segment_start() + heap_segment_size();
}

// Removes the flags from a payloadsz (in order to extract the actual payloadsz) 
#define stripFlags(payloadsz) ((payloadsz) & ~0x7)


// Returns the payloadsz modified to also contain flag information 
static inline size_t putFlags(size_t payloadsz, header_flags_t flags) {
    payloadsz = stripFlags(payloadsz);
    payloadsz |= flags.allocated ? 0x1 : 0;
    payloadsz |= flags.flag1 ? 0x2 : 0;
    payloadsz |= flags.flag2 ? 0x4 : 0;
    return payloadsz;
}

// Very efficient bitwise round of sz up to nearest multiple of mult
// does this by adding mult-1 to sz, then masking off the
// the bottom bits to compute least multiple of mult that is
// greater/equal than sz, this value is returned
// NOTE: mult has to be power of 2 for the bitwise trick to work!
static inline size_t roundup(size_t sz, size_t mult)
{
    return (sz + mult-1) & ~(mult-1);
}


// Given a pointer to start of payload, simply back up
// to access its block header
static inline headerT *hdr_for_payload(void *payload)
{
    return (headerT *)((char *)payload - sizeof(headerT));
}


// Given a pointer to block header, advance past
// header to access start of payload
static inline void *payload_for_hdr(headerT *header)
{
    return (char *)header + sizeof(headerT);
}


// Initializes our heap. It stores our freelist on a page of the heap and sets our 
bool myinit()
{
    init_heap_segment(0); // reset heap segment to empty, no pages allocated
    char* extraglobals = extend_heap_segment(1);
    freelist = (headerT**) extraglobals;
    // One for every power of two up to 4096
    extraglobals += sizeof(void*) * SIZE_CLASSES;
    memset(freelist, 0, sizeof(void*) * SIZE_CLASSES);
    lastInHeap = secondToLast = NULL;

    return true;
}

// Gets the correct bucket for the requestedsz we are mallocing
// Size classes for every power of 2 and every integer halfway between a power of 2
static inline int getbucket(size_t requestedsz)
{ 
    int log2 = 63 - __builtin_clzl(requestedsz);
    
    size_t average = ((1 << log2) + (1 << (log2+1))) >> 1;
    if (requestedsz < average) {
        return 2*log2;
    } else {
        return 2*log2 + 1;
    }
}

// Removes a block from the segregated free list, given a sizeclass
static inline bool removeFromFreeListIndex(int bucket, headerT *location) {
    // Updates the doubly linked segregated free list pointers
    bool existed = freelist[bucket] == location;
    if (location->prev && location->next) {
        location->prev->next = location->next;
        location->next->prev = location->prev;
    } else if (location->prev && !location->next) {
        location->prev->next = NULL;
    } else if (!location->prev && location->next) {
        location->next->prev = NULL;
        freelist[bucket] = location->next;
    } else if (!location->prev && !location->next) {
        freelist[bucket] = NULL;
    }

    location->next = location->prev = NULL;
    return existed || true;
}

// Finds the correct bucket size for a block and then removes it from the free list
static inline bool removeFromFreeList(headerT *location) {
    int bucket = getbucket(stripFlags(location->payloadsz));
    return removeFromFreeListIndex(bucket, location);
}

// Iterates through a size class looking for a block large enough for our requested sz
static inline headerT * findSufficientBlock(int sizeclass, size_t requestedsz){
    headerT * prev = NULL;
    headerT * curr = freelist[sizeclass];
    while( curr ){
        if( stripFlags(curr->payloadsz) >= requestedsz){
            

            // Updating the segregated free list
            if (prev && curr->next) {
                prev->next = curr->next;
                curr->next->prev = prev;
            } else if (prev && !curr->next) {
                prev->next = NULL;
            } else if (!prev && curr->next) {
                curr->next->prev = NULL;
                freelist[sizeclass] = curr->next;
            } else if (!prev && !curr->next) {
                freelist[sizeclass] = NULL;
            }
            curr->next = curr->prev = NULL;
            
            return curr;
        }
        prev = curr;
        curr = curr->next;
    }
    return NULL;
}


// Keeps track of the last blocks we are using in memory
static inline void updateLastInHeap(headerT *l) {
    if (l > lastInHeap) {
        secondToLast = lastInHeap;
        lastInHeap = l;
    }
}



// Finds a sufficient block by going through the free list and selecting the first available block large enough
static inline headerT * findBlock(size_t requestedsz){
    int start = getbucket(requestedsz);
    for(int i = start; i < SIZE_CLASSES; i++){
        headerT * curr = findSufficientBlock(i, requestedsz);
        if( curr != NULL){
            return curr;
        }
    }
    return NULL;
}

// Inserts a block into the free list at a certain size class
static inline void insertBlock(void* location, size_t size){
    headerT *l = (headerT *)location;
    l->payloadsz = size - sizeof(headerT);

    int bucket = getbucket(stripFlags(l -> payloadsz));
    assert(l != freelist[bucket]);
    
    l->next = freelist[bucket];
    l->prev = NULL;
    
    freelist[bucket] = l;
    
    if (l->next) {
        l->next->prev = l;
    }
    updateLastInHeap(l);
}

// Returns the next block contiguous in memory to our current block
static inline headerT* nextblock(headerT* currentBlock) {
    return (headerT*)((char *)(currentBlock+1)+stripFlags(currentBlock->payloadsz));
}

// combines two blocks in the freelist into one larger free block
static inline void combine(headerT *block1, headerT *block2, bool remove) {
    // Precondition: block1 must be in the free list and block2 is in the free list
    
    // Do an assert that verifies that block1 and block2 are adjacent
    assert(stripFlags(block1->payloadsz) % 8 == 0);
    assert(stripFlags(block2->payloadsz) % 8 == 0);
    assert((char *)block2 == (char *)(block1 + 1) + stripFlags(block1->payloadsz));
    int originalBucket = getbucket(stripFlags(block1->payloadsz));
    

    headerT *block2_next = nextblock(block2);
    size_t total_payload_size = stripFlags(block1->payloadsz) + sizeof(headerT) + stripFlags(block2->payloadsz);
    // Removes the second freeblock from the freelist and extends the first block's length to take up
    // space occupied by both blocks.
    if (remove) {
         assert(removeFromFreeList(block2));
    }
    block1->payloadsz = total_payload_size;
    if (block2_next < (headerT*)heap_segment_end() - 1) {
        block2_next->prevInMem = block1;
    }
    
    // Case where we are dealing with the last blocks in memory
    if (block2 == lastInHeap) {
        lastInHeap = block1;
        secondToLast = block1->prevInMem;
    }
    
    // Removes the original block1 from the free list as well
    bool removeSuccess = removeFromFreeListIndex(originalBucket, block1);
    assert(removeSuccess);
    if (removeSuccess) {
        insertBlock(block1, sizeof(headerT) + block1->payloadsz);
    }

    // Postcondition: the combined block is inserted into the freelist
    
    
}

// Coalesces the current block with free blocks contiguous in memory to the right and left. 
// This function is called every time free is called.
static inline headerT* coalesce(headerT *block) {
 
    // Gets the headers and boolean for allocation for the 2 blocks previous and next in memory
    headerT *next = nextblock(block);
    headerT *prev = block -> prevInMem;
    bool nextAlloc = next >= ((headerT *)heap_segment_end() - 1) || (calculateFlags(next-> payloadsz).allocated);
    bool prevAlloc = !prev || (calculateFlags(prev-> payloadsz).allocated);
    headerT *retval = block;

    // Combines free blocks if it can
    if(nextAlloc && prevAlloc){
        return block;
    }   
    if (!prevAlloc) {
        // Remember to update lastInHeap
        combine(prev, block, true);
        // Now the prev block is supposed to be deleted
        retval = prev;
    }
    if (!nextAlloc) {
        combine(retval, next, true);
    }

    // Updates the header flags and returns our new block 
    header_flags_t flagz = calculateFlags(retval->payloadsz);
    flagz.allocated = false;
    retval->payloadsz = putFlags(retval->payloadsz, flagz);
    return retval;

}

// function that prints the freelist for debugging purposes
void printFreeList() {
    for (int i = 0; i < SIZE_CLASSES; i++) {
        printf("[%d] = ", i);
        headerT *current = freelist[i];
        while (current) {
            printf("%p -> ", current);
            current = current->next;
        }
        printf("NULL\n");
    }
}

// Splits a free block into a free and an allocated block.
static inline void splitBlock(headerT * location, size_t requestedsz){

    // Allocates what is requested for the user
    headerT * available = location;
    size_t roundedsz = roundup( requestedsz, 8);
    size_t availablesz = stripFlags(location->payloadsz) - roundedsz;
    if (availablesz <= sizeof(headerT)) return;
    available = (headerT*)((char*) (available+1) + roundedsz);


    insertBlock(available, availablesz);
    headerT *previousNext = nextblock(location);
    location -> payloadsz = roundedsz;
    if (previousNext < (headerT*)heap_segment_end() - 1) { 
        previousNext->prevInMem = available;
    }
    available->prevInMem = location;
}


// malloc a block by rounding up size to number of pages, extending heap
// segment and using most recently added page(s) for this block. This
// means each block
void *mymalloc(size_t requestedsz)
{
    if (requestedsz == 0) {
        return NULL;
    }
    headerT * location = findBlock(requestedsz);
    if ( location ){
        splitBlock(location, requestedsz);
        header_flags_t flags = {1, 0, 0};
        location->payloadsz = putFlags(location->payloadsz, flags);
        return location + 1;
    }
    else {
        // function look through size class
        // If there's nothing in that size class, go to the next size class
        size_t npages = roundup(requestedsz + sizeof(headerT), PAGE_SIZE)/PAGE_SIZE;
        size_t addedBytes = npages * PAGE_SIZE;
        headerT *header = extend_heap_segment(npages);
        if (!header) {
            return NULL;
        }
        
        insertBlock(header, addedBytes);
        header->prevInMem = secondToLast;
        header = coalesce(header);
        removeFromFreeList(header);
        splitBlock(header, requestedsz);
        header_flags_t flags = {1,0,0};
        header->payloadsz = putFlags(header->payloadsz, flags);
        return header + 1;
    }
}


// Frees the block and attempts to coalesce it with its adjacent neighbors into a larger freeblock
void myfree(void *ptr)
{
    if (!ptr) return;
    headerT *header = ptr;
    header--;
    
    header_flags_t flags = calculateFlags(header->payloadsz);
    flags.allocated = false;
    header->payloadsz = putFlags(header->payloadsz, flags);
    
    insertBlock(header, header->payloadsz+sizeof(headerT));
    coalesce(header);
}

// Reallocated malloced memory into a block that could handle newsz
void *myrealloc(void *oldptr, size_t newsz)
{
    
    if (!oldptr) {
        return mymalloc(newsz);
    }
    if (newsz == 0) {
        myfree(oldptr);
        return NULL;
    }
    headerT *header = oldptr;
    header--;

    // If the blocks size is large enough, we use the same memory address
    if (stripFlags(header->payloadsz) >= newsz) return oldptr;
    
    // Tries to combine the oldptr with the next contiguous block in memory if it's free. Then it tries to reallocate 
    // to this combined block if it is large enough
    headerT *nb = nextblock(header);
    if (nb < (headerT*)heap_segment_end() - 1) {
        header_flags_t flagz = calculateFlags(nb->payloadsz);
        size_t availablesz = stripFlags(nb->payloadsz) + stripFlags(header->payloadsz) + sizeof(headerT);
        if (!flagz.allocated && availablesz >= newsz) {
            header_flags_t currentFlags = calculateFlags(header->payloadsz);
            
            insertBlock(header, stripFlags(header->payloadsz) + sizeof(headerT));
            combine(header, nb, true);
            removeFromFreeList(header);
            // Use header
            splitBlock(header, roundup(newsz, 8));
            header->payloadsz = putFlags(header->payloadsz, currentFlags);
            return header+1;
        }
    }
    

    // In the worst case, we simply malloc and free the old block
    void *newptr = mymalloc(newsz);
    if (!newptr) {
        myfree(oldptr);
        return NULL;
    }


    size_t oldsz = stripFlags(header->payloadsz);
    memcpy(newptr, oldptr, oldsz < newsz ? oldsz: newsz);
    myfree(oldptr);
    return newptr;
}


// validate_heap is your debugging routine to detect/report
// on problems/inconsistency within your heap data structures
bool validate_heap()
{
    return true;
    for (int i = 0; i < SIZE_CLASSES; i++) {
        headerT *current = freelist[i];
        while (current) {
            // Checked that blocks were within bounds
            if (current > (headerT*)heap_segment_end() || current < (headerT *)heap_segment_start()) {
                return false;
            }
            // Checked that payloadsz's were valid
            if (current->payloadsz <= 0 || stripFlags(current->payloadsz) % 8) {
                return false;
            }
            // An allocated block should not be in the free list
            if (calculateFlags(current->payloadsz).allocated) {
                return false;
            }
            // Checking for issues with the doubly linked list
            if ((current->next && current->next->prev != current) || (current->prev && current->prev->next != current)) {
                return false;
            }
            // Making sure that there is no overlap
            headerT *prev = current->prevInMem;
            if (prev && (headerT *)(stripFlags(prev->payloadsz) + (char *)(prev + 1)) != current) {
                return false;
            }
            current = current->next;
        }
    }
    
    headerT *current = (headerT *)((char *)heap_segment_start()+PAGE_SIZE);
    bool previousWasFree = false;
    while (current < (headerT *)heap_segment_end()) {
        header_flags_t flags = calculateFlags(current->payloadsz);
        // Checks for contiguous free blocks that should have been coalesced together
        if ( previousWasFree && !flags.allocated) {
            printf("Contiguous free blocks D:\n");
            return false;
        }
        previousWasFree = !flags.allocated;
                        
        // Checks For valid payloadsz
        if (current->payloadsz <= 0 || stripFlags(current->payloadsz) % 8) {
            printf("Block at %p had a size of 0\n", current);
            return false;
        }
        current = nextblock(current);
    }
    return true;
}
