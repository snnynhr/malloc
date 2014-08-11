/*
 * mm.c
 * anahar - Sunny Nahar
 * 
 * Implementation of Malloc - The following solution implements
 * a memory allocator using segregated lists and best fits. All
 * the general operations are supported, malloc, free, realloc,
 * and calloc. 
 * There are 16 segregated lists used with different bin sizes,
 * which start linear and grow hyper-exponentially. 
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"

/* Basic constants and macros */
#define VERBOSE 0
#define HEAP_PRINT 1

#define SMALL 0
#define LARGE 4

#define PFREE 0
#define PALLOC 2

#define FREE 0
#define ALLOC 1

#define HSIZE 2 /* Header size */
#define WSIZE 4 /* Word size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */

#define MINSIZE 16 /* Minimum block size (bytes) */
#define CHUNKSIZE 192 /* Extend heap by this amount (bytes) */
#define SEGSIZE 16 /* Number of segregated lists */

#define passert(cond) if(!(cond)) print_checkheap(); assert(cond);

// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                        printf("Checkheap failed on line %d\n", __LINE__);\
                        exit(-1);  \
                        }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif

/*
 * Global vars - (Defined early since they are used in inline functions)
 */
static char *heap_start; /* Points to the start of the heap */
static char *wilderness; /* Points to the wilderness */
static char *heap_end; /* Points to the end of the heap */
static uint32_t *seg_list;

static uint32_t num = 0;
static uint32_t tot = 0;
static uint32_t alloc = 0;
/*
 *  Heap Check functions
 *  
 *  These are used in the mm_checkheap function to ensure
 *  there is no corruption.
 */

// Align p to a multiple of w bytes
static inline void* align(const void const* p, unsigned char w) {
    return (void*)(((uintptr_t)(p) + (w-1)) & ~(w-1));
}

// Check if the given pointer is 8-byte aligned
static inline int aligned(const void const* p) {
    return align(p, 8) == p;
}

// Return whether the pointer is in the heap.
static inline int in_heap(const void* p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}


/*
 * Block manipulation functions
 *
 * These access and change components of a memory block
 * including size and allocation. 
 */

static inline uint32_t get_offset(void* const p);
static inline void* get_address(uint32_t const p);
static inline void set16(void* const p, uint16_t val);
static inline uint32_t get16(void* const p);
static inline void set32(void* const p, uint32_t val);
static inline uint32_t get32(void* const p);
static inline uint16_t pack16(size_t size, uint16_t large, uint16_t prev, uint16_t alloc);
static inline uint32_t pack32(size_t size, uint32_t large, uint32_t prev, uint32_t alloc);
static inline void setH(void* const p, size_t size, uint32_t prev, uint32_t alloc);
static inline void setF(void* const p, size_t size, uint32_t prev, uint32_t alloc);
static inline uint32_t get_size(void* const p);
static inline uint32_t get_alloc(void* const p);
static inline uint32_t get_large(void* const p);
static inline uint32_t get_palloc(void* const p);
static inline void set_alloc(void* const p, uint16_t val);
static inline void set_large(void* const p, uint16_t val);
static inline void set_palloc(void* const p, uint16_t val);
static inline void* hdrp(void* const p);
static inline void* ftrp(void* const p);
static inline void* next_blkp(void* const p);
static inline void* prev_blkp(void* const p);
static inline uint32_t geth_size(void* const p);
static inline uint32_t getf_size(void* const p);

//Get 32bit offset of 64bit address relative to heap
static inline uint32_t get_offset(void* const p)
{
    REQUIRES(p != NULL);
    REQUIRES(in_heap(p));
    
    uint64_t offset = (char*)p - (char*)mem_heap_lo();
    ASSERT(offset < 1U << 31);
   
    /* Make sure offset doesn't corrupt seglist and prologue */
    ASSERT(offset >= (SEGSIZE+2)*WSIZE);
    return (uint32_t) offset;
}
//Translate offset to address
static inline void* get_address(uint32_t const p)
{
    void* ret = (void*) ((char*)mem_heap_lo() + p);
    ASSERT(in_heap(ret));
    return ret;
}
//Set the value of a pointer
static inline void set16(void* const p, uint16_t val)
{
    REQUIRES(in_heap(p));
    *((uint16_t*)p) = val;
}
//Get the value of a pointer
static inline uint32_t get16(void* const p)
{
    REQUIRES(in_heap(p));
    return *((uint16_t*)p);
}
//Set the value of a pointer
static inline void set32(void* const p, uint32_t val)
{
    REQUIRES(in_heap(p));
    *((uint32_t*)p) = val;
}
//Get the value of a pointer
static inline uint32_t get32(void* const p)
{
    REQUIRES(in_heap(p));
    return *((uint32_t*)p);
}
//Combine the set with the alloc bit
static inline uint16_t pack16(size_t size, uint16_t large, uint16_t prev, uint16_t alloc)
{
    REQUIRES(size < 65536);
    REQUIRES(large == LARGE || large == SMALL);
    REQUIRES(prev == PALLOC || prev == PFREE);
    REQUIRES(alloc == ALLOC || alloc == FREE);
    return size | large | prev | alloc;
}
//Combine the set with the alloc bit
static inline uint32_t pack32(size_t size, uint32_t large, uint32_t prev, uint32_t alloc)
{
    REQUIRES(large == LARGE || large == SMALL);
    REQUIRES(prev == PALLOC || prev == PFREE);
    REQUIRES(alloc == ALLOC || alloc == FREE);
    return size | large | prev | alloc;
}
static inline void setH(void* const p, size_t size, uint32_t prev, uint32_t alloc)
{
    REQUIRES(prev == PALLOC || prev == PFREE);
    REQUIRES(alloc == ALLOC || alloc == FREE);
    REQUIRES(in_heap(p) || p == ((char*)mem_heap_hi()+1));
    if(size < 65536)
    {
        set16(hdrp(p), pack16((uint16_t)size, (uint16_t)SMALL, (uint16_t)prev, (uint16_t)alloc));
    }
    else
    {
        set16(hdrp(p), pack16(65528, (uint16_t)LARGE, (uint16_t)prev, (uint16_t)alloc));
        set32((char*)(p) + WSIZE, pack32(size, LARGE, prev, alloc));
    }
}
static inline void setF(void* const p, size_t size, uint32_t prev, uint32_t alloc)
{
    REQUIRES(prev == PALLOC || prev == PFREE);
    REQUIRES(alloc == ALLOC || alloc == FREE);
    REQUIRES(in_heap(p));
    if(size < 65536)
    {
        set16(ftrp(p), pack16((uint16_t)size, (uint16_t)SMALL, (uint16_t)prev, (uint16_t)alloc));
    }
    else
    {
        set16(ftrp(p), pack16(65528, (uint16_t)LARGE, (uint16_t)prev, (uint16_t)alloc));
        set32(((char *)(ftrp(p)) - WSIZE), pack32(size, LARGE, prev, alloc));
    }
}
//Get the size from the header/footer block
static inline uint32_t get_size(void* const p)
{
    REQUIRES(in_heap(p));
    if(get_large(p))
        return get32(((char *)(p) + HSIZE)) & (~0x7);
    return get16(p) & (~0x7);
}
//Get allocated bit from header/footer block
static inline uint32_t get_alloc(void* const p)
{
    REQUIRES(in_heap(p));
    return get16(p) & (0x1);
}
//Get allocated bit from header/footer block
static inline uint32_t get_large(void* const p)
{
    REQUIRES(in_heap(p));
    return (get16(p) & (0x4))>>2;
}
//Get allocated bit from header/footer block
static inline uint32_t get_palloc(void* const p)
{
    REQUIRES(in_heap(p));
    return (get16(p) & (0x2));
}
//Get allocated bit from header/footer block
static inline void set_alloc(void* const p, uint16_t val)
{
    REQUIRES(val == ALLOC || val == FREE);
    REQUIRES(in_heap(p));
    set16(p, (get16(p) & ~(0x1)) | val);
}
//Get allocated bit from header/footer block
static inline void set_large(void* const p, uint16_t val)
{
    REQUIRES(val == LARGE || val == SMALL);
    REQUIRES(in_heap(p));
    set16(p, (get16(p) & ~(0x4)) | val);
}
//Get allocated bit from header/footer block
static inline void set_palloc(void* const p, uint16_t val)
{
    REQUIRES(val == PALLOC || val == PFREE);
    REQUIRES(in_heap(p));
    set16(p, (get16(p) & ~(0x2)) | val);
}

//Get pointer to header block
static inline void* hdrp(void* const p)
{
    REQUIRES(in_heap(p) || (p == ((char*)mem_heap_hi()+1)));
    return ((char *)(p) - HSIZE);
}
//Get pointer to footer block
static inline void* ftrp(void* const p)
{
    REQUIRES(in_heap(p));
    return ((char *)(p) + geth_size(p) - WSIZE);
}
//Get pointer to next block
static inline void* next_blkp(void* const p)
{
    REQUIRES(in_heap(p));
    return ((char *)(p) + geth_size(p));
}
//Get pointer to previous block
static inline void* prev_blkp(void* const p)
{
    REQUIRES(in_heap(p) || (p == ((char*)mem_heap_hi()+1)));
    void* const q = (char*)(p) - WSIZE;
    uint32_t size;
    if(get_large(q))
        size = get32((char*)q - WSIZE) & ~(0x7);
    else
        size = get16((char*)q) & ~(0x7);
    return (char*)(p) - size;
}
static inline uint32_t geth_size(void* const p)
{
    void* const q = hdrp(p);
    if(get_large(q))
        return get32(((char *)(p) + WSIZE)) & ~(0x7);
    else
        return get16(q) & ~(0x7);
}
static inline uint32_t getf_size(void* const p)
{
    if(get_large(hdrp(p)))
        return get32((char*)ftrp(p) - WSIZE) & ~(0x7);
    else
        return get16(ftrp(p)) & ~(0x7);
}

/*
 * Segregated List functions
 *
 * These functions manipulate the segregated lists, 
 * getting and setting forward and previous free blocks.
 */
// Get offset of previous free block
static inline uint32_t get_prev(void* p)
{
    REQUIRES(in_heap(p));
    return get32((char*)(p) + DSIZE*get_large(hdrp(p)));
}
//Get offset of next free block
static inline uint32_t get_next(void* p)
{
    REQUIRES(in_heap(p));
    return get32((char*)(p) + WSIZE + DSIZE*get_large(hdrp(p)));
}
//Set offset of prev free block
static inline void set_prev(void* p, uint32_t val)
{
    REQUIRES(in_heap(p));
    set32((char*)(p) + DSIZE*get_large(hdrp(p)), val);
}
//Set offset of next free block
static inline void set_next(void* p, uint32_t val)
{
    REQUIRES(in_heap(p));
    set32((char*)(p) + WSIZE + DSIZE*get_large(hdrp(p)), val);
}
/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing malloc implementation.
 */

/*
 * Get the corresponding index of the segregated list.
 */ 
static inline size_t get_index(size_t asize)
{
    REQUIRES(asize >= MINSIZE);
    
    if(asize <= 48)
        return (asize >> 3) - 2;
    
    if(asize <= 72) return 5;
    if(asize <= 136) return 6;
    if(asize <= 264) return 7;
    if(asize <= 520) return 8;
    if(asize <= 1032) return 9;
    if(asize <= 2056) return 10;
    if(asize <= 4104) return 11;
    if(asize <= 16392) return 12;
    if(asize <= 32774) return 13;
    if(asize <= 262152) return 14;
    return 15;
}

/*
 * Adds free block to the appropriate seg-list
 */
static void add_free_block(void *ptr)
{
    REQUIRES(ptr != wilderness);
    REQUIRES(get_alloc(hdrp(ptr)) == 0);

    /* Get ptr data */
    size_t size = geth_size(ptr);
    size_t index = get_index(size);
    uint32_t last = seg_list[index];

    /* If ptr is the start of the seg_list */
    if(last == 0)
    {
        seg_list[index] = get_offset(ptr);

        /* Update links */
        set_prev(ptr, 0);
        set_next(ptr, 0);
    }
    else
    {
        /* ptr is somewhere in the middle */
        size_t offset = get_offset(ptr);
        seg_list[index] = offset;

        /* Update links */
        set_prev(ptr, last);
        set_next(ptr, 0);
        set_next(get_address(last), offset);
    }

    ASSERT(seg_list[index] != last);
}

/*
 * Removes free block from the appropriate seg-list 
 */
static inline void remove_free_block(void *ptr)
{
    REQUIRES(get_alloc(hdrp(ptr)) == 0);
    REQUIRES(ptr != wilderness);

    /* Get ptr data */
    size_t size = geth_size(ptr);
    size_t index = get_index(size);
    uint32_t last = seg_list[index];
    uint32_t offset = get_offset(ptr);

    if(last == offset)
    {
        /* Pointer is the front of the seglist */
        uint32_t prev = get_prev(ptr);
        seg_list[index] = prev;
        if(prev != 0)
            set_next(get_address(prev),0);
    }
    else
    {
        /* Pointer is somewhere in the middle of the seg_list */
        if(get_prev(ptr) == 0) /* Check if head of list */
            set_prev(get_address(get_next(ptr)),0);
        else
        {
            /* Update links */
            set_prev(get_address(get_next(ptr)),get_prev(ptr));
            set_next(get_address(get_prev(ptr)),get_next(ptr));   
        }
    }
}

/*
 * Coalesces adjacent free blocks into one free block
 * Removes the old free blocks from the appropriate seglists
 */
static void *coalesce(void *bp)
{
    REQUIRES(in_heap(bp));
    /* Get surrounding blocks */
    void* next = next_blkp(bp);

    /* Get block data */
    size_t prev_alloc = get_palloc(hdrp(bp));
    size_t next_alloc = get_alloc(hdrp(next));
    size_t size = geth_size(bp);

    if (prev_alloc && next_alloc) { /* Case 1 */
        //setH(bp, size, PALLOC, FREE);
        //setF(bp, size, PALLOC, FREE);
        set_alloc(ftrp(bp), FREE);
        return bp;
    }

    else if (prev_alloc && !next_alloc) { /* Case 2 */
        size += geth_size(next);

        /* Wilderness case */
        if(next != wilderness)
            remove_free_block(next);

        /* Update headers */
        setH(bp, size, PALLOC, FREE);
        setF(bp, size, PALLOC, FREE);
    }

    else if (!prev_alloc && next_alloc) { /* Case 3 */
        void* prev = prev_blkp(bp);
        uint32_t pr = get_palloc(hdrp(prev));
        size += geth_size(prev);

        /* Wilderness Case */
        if(prev != wilderness)
            remove_free_block(prev);

        /* Update headers */
        setH(prev, size, pr, FREE);
        setF(prev, size, pr, FREE);
        bp = prev_blkp(bp);
    }

    else { /* Case 4 */
        void* prev = prev_blkp(bp);
        size += geth_size(prev) +
        geth_size(next);

        /* Wilderness case */
        if(prev != wilderness)
            remove_free_block(prev);
        if(next != wilderness)
            remove_free_block(next);

        /* Update headers */
        setH(prev, size, PALLOC, FREE);
        setF(next, size, PALLOC, FREE);
        bp = prev;
    }
    ASSERT(in_heap(bp));
    return bp;
}

/*
 * Finds a free block large enough to fit a block of size asize
 */ 
static void *find_fit(size_t asize)
{
    size_t index = get_index(asize); 
    
    /* Search through seg_lists, Perform best fit search */
    for (int i = index; i < SEGSIZE; i++)
    {
        /* 
         * Large block optimization:
         * For large blocks, we don't want small block sizes to eat
         * out of them, in case another large block is allocated.
         * Therefore we relegate the smaller blocks to the wilderness
         * if there is no space. 
         */
        //if(i >= 13 && index <= 5) 
        //    break;
        
        /* Check if seg_list is empty */
        if(seg_list[i] != 0)
        {
            uint32_t p = seg_list[i];
            void* address = get_address(p);

            ASSERT(get_alloc(hdrp(address)) == 0);

            uint32_t min = ~0;
            void* min_add = NULL;

            /* Check first element of seglist */
            size_t address_size = geth_size(address);
            if(address_size >= asize && (address_size - asize < min))
            {
                min = address_size - asize;
                min_add = address;
                /*
                 * For seglist 0 to 4, the lists contain only one
                 * size. Therefore if there exists a first element
                 * we return it.  
                 */
                if(i <= 4) 
                {
                    remove_free_block(address);
                    return address;
                }
            }
            
            /* Iterate through rest of seglist */
            p = get_prev(get_address(p));

            while(p != 0)
            {
                void* address = get_address(p);
                uint32_t np = get_prev(address);

                /* Check if size is at least block size */
                size_t address_size = geth_size(address);
                if(address_size >= asize && (address_size - asize < min))
                {
                    min = address_size - asize;
                    min_add = address;
                }
                p = np; /* OMG LULZ! */
            }

            /* If there exists a minimum, we return the address */
            if(min_add != NULL)
            {
                remove_free_block(min_add);
                return min_add;
            }
        }
    }

    /* If no space in seglist, check the wilderness */
    if (asize <= geth_size(wilderness) - MINSIZE)
    {
        return wilderness;
    }
    return NULL; /* No fit */
}

/*
 * Place a memory block at the respected pointer, while
 * creating a free block if there is excess space an
 * adding it to the segregated list.
 */
static void place(void *bp, size_t asize)
{
    REQUIRES(in_heap(bp));
    REQUIRES(get_alloc(hdrp(bp))==FREE);
    size_t csize = geth_size(bp);
    
    bool flag = false;
    if(bp == wilderness)
        flag = true;

    /* Check if there is enough space for another block */
    if ((csize - asize) >= MINSIZE) {
        /* Set current block as allocated */
        setH(bp, asize, PALLOC, ALLOC);
        
        /* Separate block to create a new free block */
        bp = next_blkp(bp);
        setH(bp, csize-asize, PALLOC, FREE);
        setF(bp, csize-asize, PALLOC, FREE);
        set_palloc(hdrp(next_blkp(bp)), PFREE);
        /* Add to free list if its not in the wilderness */
        if(!flag)
            add_free_block(bp);
        else
            wilderness = bp;
    }
    else {
        /* Wilderness block should NEVER reach here */
        ASSERT(geth_size(wilderness) >= MINSIZE);

        /* Otherwise set allocated block */
        setH(bp, csize, PALLOC, ALLOC);
        setF(bp, csize, PALLOC, ALLOC);
        set_palloc(hdrp(next_blkp(bp)), PALLOC);
    }
}

/*
 * Extends the heap by a fixed size
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    alloc += size;

    /* Initialize free block header/footer and the epilogue header */
    uint32_t a = get_alloc(hdrp(wilderness));
    setH(bp, size, PALLOC*a, FREE); /* Free block header */
    setF(bp, size, PALLOC*a, FREE); /* Free block footer */
    heap_end = next_blkp(bp);
    setH(heap_end, 0, PFREE, ALLOC); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * Initialize: return -1 on error, 0 on success.
 * 
 * Initializes the heap, creating 
 */
int mm_init(void) {
    /* Create the initial empty heap */
    if ((heap_start = mem_sbrk((2+SEGSIZE)*WSIZE)) == (void *)-1)
        return -1;

    alloc += 72;

    /* Initialize seg_list */
    seg_list = (uint32_t*)heap_start;
    for(int i = 0; i<SEGSIZE; i++)
        set32(heap_start + (i*WSIZE), 0);
    
    heap_start += SEGSIZE*WSIZE;

    /* Set buffer header */
    set16(heap_start, 0); /* Alignment padding */
    /*
        We set prologue header size 0 instead of 4, since 4
        inteferes with a restricted bit (large bit).
    */
    setH(heap_start + (WSIZE), 0, PFREE, ALLOC); /* Prologue header */
    setF(heap_start + (WSIZE), 0, PFREE, ALLOC); /* Prologue footer */
    setH(heap_start + (2*WSIZE), 0, PALLOC, ALLOC); /* Epilogue header */
    
    alloc += 8;

    /* Set global pointers */
    heap_start += WSIZE;
    heap_end = heap_start + WSIZE;

    wilderness = heap_start + WSIZE;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * Implementation of the malloc routine
 *
 * malloc returns a pointer to the memory of a specific size.
 */
void *malloc (size_t size) {
    checkheap(VERBOSE);  // Let's make sure the heap is ok!
    size_t asize; /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;
    if(HEAP_PRINT)
        printf("Num %u. Usage: %u.  Allocated: %u. Efficiency: %f. %zu\n", num, tot, alloc, (double)tot/alloc, size);
    num++;
    tot += size;
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */

    asize = ((size+1)/DSIZE)*DSIZE + DSIZE;
    if(size <= DSIZE - 2)
        asize += DSIZE;
    if(asize >= 65536)
    {
        asize += 2*DSIZE;
        /* Search the free list for a fit */
        if ((bp = find_fit(asize)) != NULL) {
            place(bp, asize);
            return (char*)bp + DSIZE;
        }
        else
        {
            /* No fit found. Get more memory and place the block */

            /* Check the wilderness for space */
            size_t wild = geth_size(wilderness);
            size_t nsize = asize;
            if(asize >= wild - MINSIZE)
                nsize -= wild - MINSIZE;
            
            /* We allocate at least the chunksize */
            extendsize = nsize > CHUNKSIZE ? nsize : CHUNKSIZE;
            if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
                return NULL;
            place(bp, asize);
            return (char*)bp + DSIZE;
        }
    }
    else
    {
        /* Search the free list for a fit */
        if ((bp = find_fit(asize)) != NULL) {
            place(bp, asize);
            return bp;
        }
        else
        {
            /* No fit found. Get more memory and place the block */

            /* Check the wilderness for space */
            size_t wild = geth_size(wilderness);
            size_t nsize = asize;
            if(asize >= wild - MINSIZE)
                nsize -= wild - MINSIZE;
            
            /* We allocate at least the chunksize */
            extendsize = nsize > CHUNKSIZE ? nsize : CHUNKSIZE;
            if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
                return NULL;
            place(bp, asize);
            return bp;
        }
    }
}

/*
 * Free routine.
 *
 * Frees the memory at a given pointer, and creates a new free block.
 */
void free (void *ptr) {
    REQUIRES(ptr == NULL || (in_heap(ptr) && get_alloc(hdrp(ptr))));
    checkheap(VERBOSE);
    if(HEAP_PRINT)
        printf("Num %u. Usage: %u.  Allocated: %u. Efficiency: %f. %zu\n", num, tot, alloc, (double)tot/alloc, size);
    /* If pointer is null, return */    
    if (ptr == NULL) {
        return;
    }
    uint32_t is_large = get_large(hdrp(ptr));
    if(is_large)
    {
        ptr = (char*)(ptr) - DSIZE;
    }
    size_t size = geth_size(ptr);

    tot -= size;

    uint32_t pr = get_palloc(hdrp(ptr));
    /* Set allocated to 0 */
    setH(ptr, size, pr, FREE);
    setF(ptr, size, pr, FREE);
    set_palloc(hdrp(next_blkp(ptr)), PFREE);
    /* Handle reset of wilderness */

    /* Check if pointer is behind the wilderness 
       since during free, it will be coalesced */
    bool flag = false;
    if(get_palloc(hdrp(wilderness)) == PFREE && ptr == prev_blkp(wilderness))
        flag = true;  
    
    ptr = coalesce(ptr);
    
    /* If pointer is not in the wilderness, add it to the seg_list */
    if(flag)
        wilderness = ptr;
    else
    {
        add_free_block(ptr);
        set_palloc(hdrp(next_blkp(ptr)), PFREE);
    }
    checkheap(VERBOSE);
}

/*
 * Realloc routine. 
 *
 * Realloc returns a pointer to memory with the specificied size
 * which contains the data from the old pointer.
 */
void *realloc(void *oldptr, size_t size) {
    REQUIRES(in_heap(oldptr) || oldptr == NULL);
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(oldptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return malloc(size);
    }
    
    //void* p = next_blkp(oldptr);
    //size_t old = get_size(hdrp(oldptr)) - DSIZE;
    //size_t asize = DSIZE*((size + DSIZE - 1)/DSIZE);
    //size_t asize = ((size+1)/DSIZE)*DSIZE + DSIZE;
    //if(size <= DSIZE - 2)
    //    asize += DSIZE;
    //if(asize >= 65536)
    //    asize += 2*DSIZE;
    /* If realloc size is less than old size, then return the old
       pointer. If possible, create a new free block with the
       extra space */
    /*
    if(asize <= old) 
    {
        *//* Not enough space for another free block *//*
        if(old - asize <= MINSIZE)
            return oldptr;
        else
        {
            *//* Alloc new size *//*
            set(hdrp(oldptr), pack(asize + DSIZE, 1));
            set(ftrp(oldptr), pack(asize + DSIZE, 1));
            void* bp = next_blkp(oldptr);

            *//* Create new free block *//*
            set(hdrp(bp), pack(old - asize, 0));
            set(ftrp(bp), pack(old - asize, 0));
            add_free_block(bp);
            return oldptr;
        }
    }
    */
    /* Check if the next block is free, and if there is
       enough space to realloc into the next block *//*
    void* hd = hdrp(p);
    if(!get_alloc(hd) && asize - old <= get_size(hd) && 
       (get_size(hd) - (asize-old) >= MINSIZE))
    {
        *//* Make sure we don't remove the wilderness *//*
        if(p != wilderness)
            remove_free_block(p);
        
        *//* Get normalized size *//*
        asize = DSIZE*(((size - old) + DSIZE - 1)/DSIZE); 
        
        *//* Place the block *//*
        place(p, asize);
        set(hdrp(oldptr), pack(old + asize + DSIZE, 1));
        set(ftrp(oldptr), pack(old + asize + DSIZE, 1));
        newptr = oldptr;
    }
    else
    {
        */
        /* Otherwise, we need to find somewhere else to realloc */
        newptr = malloc(size);
        
        /* If realloc() fails the original block is left untouched  */
        if(!newptr)
            return 0;

        /* Copy the old data. */
        if(get_large(hdrp(oldptr)))
        {
            oldsize = geth_size((char*)(oldptr) - DSIZE) - 18;
            if(size < oldsize) 
                oldsize = size;
            memcpy(newptr, oldptr, oldsize);
        }
        else
        {
            oldsize = geth_size(oldptr)-2;
            if(size < oldsize) 
                oldsize = size;
            memcpy(newptr, oldptr, oldsize);
        }

        /* Free the old block. */
        free(oldptr);
    //}
    checkheap(VERBOSE);
    return newptr;
}

/*
 * calloc routine
 *
 * Allocates a specified amount of memory and initializes it.
 */
void *calloc (size_t nmemb, size_t size) {
    /* Get total size */
    size_t bytes = nmemb * size;
    void *newptr;

    /* Get memory from malloc */
    newptr = malloc(bytes);

    /* Init memory */
    memset(newptr, 0, bytes);

    return newptr;
}

void print_checkheap() {
    void *bp;
    printf("Prologue %p: HD %d\tALLOC %d, PALLOC %d, LARGE %d\n", heap_start, 
        geth_size(heap_start), get_alloc(hdrp(heap_start)), 
        get_palloc(hdrp(heap_start)), get_large(hdrp(heap_start)));
    for (bp = heap_start+WSIZE; geth_size(bp) !=0; bp = next_blkp(bp))
    {
        if(get_alloc(hdrp(bp)))
            printf("Checking %p: HD %d\tALLOC %d, PALLOC %d, LARGE %d.\n",
                bp, geth_size(bp), get_alloc(hdrp(bp)), get_palloc(hdrp(bp)), 
                get_large(hdrp(bp)));
        else
            printf("Checking %p: HD %d, FT %d, ALLOC %d,%d PALLOC %d,%d LARGE %d,%d\n\t HEADER: %p FOOTER: %p\n",
                bp, geth_size(bp), getf_size(bp), get_alloc(hdrp(bp)), 
                get_alloc(ftrp(bp)), get_palloc(hdrp(bp)), 
                get_palloc(ftrp(bp)), get_large(hdrp(bp)), 
                get_large(ftrp(bp)), hdrp(bp), ftrp(bp));
    } 
    printf("Epilogue %p: HD %d\tALLOC %d, PALLOC %d, LARGE %d\n", heap_end, 
        geth_size(heap_end), get_alloc(hdrp(heap_end)), 
        get_palloc(hdrp(heap_end)), get_large(hdrp(heap_end))); 
    printf("Wilderness %p\n", wilderness);
}

/*
 * mm_checkheap:
 * Returns 0 if no errors were found, otherwise returns the error
 */
int mm_checkheap(int verbose) {
    void *bp;

    if(verbose)
        printf("Entering Checkheap.\n");

    if(verbose)
        printf("Checking Prologue.\n");

    /* Check Prologue */

    passert(geth_size(heap_start) == 0);
    passert(get_alloc(hdrp(heap_start)) == ALLOC);
    bool is_free = false;
    uint32_t free_block_count = 0;
    uint32_t is_alloc = get_alloc(hdrp(heap_start));
    for (bp = heap_start+WSIZE; geth_size(bp) !=0; bp = next_blkp(bp))
    {
        if(verbose && get_alloc(hdrp(bp)))
            printf("Checking %p: HD %d, ALLOC %d, PALLOC %d.\n", 
             bp, geth_size(bp), get_alloc(hdrp(bp)), get_palloc(hdrp(bp)));
        else if(verbose && !get_alloc(hdrp(bp)))
            printf("Checking %p: HD %d, FT %d, ALLOC %d, PALLOC %d.\n", 
             bp, geth_size(bp), getf_size(bp), get_alloc(hdrp(bp)), get_palloc(hdrp(bp)));
        
        /* Check heap block consistency */
        passert(in_heap(bp));
        passert(aligned(bp));
        passert(geth_size(bp) >= MINSIZE);
        if(get_alloc(hdrp(bp)) == 0)
        {
            passert(geth_size(bp) == getf_size(bp));
            passert(get_alloc(hdrp(bp)) == get_alloc(ftrp(bp)));
            passert(get_palloc(hdrp(bp)) == get_palloc(ftrp(bp)));
            passert(get_large(hdrp(bp)) == get_large(ftrp(bp)));
        }
        passert(geth_size(bp) == (char*)ftrp(bp)-(char*)hdrp(bp) + HSIZE);
        passert(get_palloc(hdrp(bp))/PALLOC == is_alloc);
        is_alloc = get_alloc(hdrp(bp));
        if(get_alloc(hdrp(bp)) == 0)
        {
            /* No consecutive free blocks */
            passert(!is_free);
            is_free = true;
            free_block_count++;
        }
        else
        {
            is_free = false;
        }
    }

    /* Epilogue */

    /* heap_end is one more then allocated heap max */
    REQUIRES(bp == ((char*)mem_heap_hi() + 1));
    passert(bp == heap_end);
    
    /* Check epilogue block conditions */
    passert(geth_size(bp) == 0);
    passert(get_alloc(hdrp(bp)) == 1);

    /* Make sure the previous block is the wilderness */
    passert(prev_blkp(bp) == wilderness);
    
    if(verbose)
        printf("Checking seglists.\n");
    
    uint32_t seg_list_count = 0;
    for(int i = 0; i < SEGSIZE; i++)
    {
        uint32_t p = seg_list[i];
        while(p != 0)
        {
            seg_list_count++;
            void* bp = get_address(p);

            if(verbose)
                printf("Checking pointer in seglist %d: %p. Size: %x\n",i,bp,get_size(hdrp(bp)));
            
            /* Check block consistency of seg_list free block */
            passert(in_heap(bp));
            passert(aligned(bp));
            passert(geth_size(bp) >= MINSIZE);
            if(get_alloc(hdrp(bp)) == 0)
            {
                passert(geth_size(bp) == getf_size(bp));
                passert(get_alloc(ftrp(bp)) == 0);
            }
            passert(get_alloc(hdrp(bp)) == 0);
            //passert(get_size(hdrp(bp))==(char*)ftrp(bp)-(char*)hdrp(bp)+WSIZE);
            
            /* Check link structure */
            uint32_t nl = get_next(bp);
            uint32_t np = get_prev(bp);
            
            if(np != 0)
                passert(get_next(get_address(np)) == p);
            if(nl != 0)
                passert(get_prev(get_address(nl)) == p);
            p = np;
        }
    }

    /* Check if the seglist has all the possible free blocks
       Remember that the wilderness block is free, but doesn't count
       as a seg_list block, there it is included in the free count,
       but not in the seg count */
    passert(free_block_count == seg_list_count + 1);
    return 0;
}