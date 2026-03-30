#include "types.h"
#include "memlayout.h"
#include "elf.h"
#include "riscv.h"
#include "mem.h"
#include "string.h"
#include "console.h"
#include "trap.h"
#include "proc.h"

// Extern Globals
extern pagetable_t kernel_pagetable; // mem.c
extern char trampoline[]; // trampoline.S
extern char _binary_user_init_start; // The user init code

////////////////////////////////////////////////////////////////////////////////
// Static Definitions and Helper Function Prototypes
////////////////////////////////////////////////////////////////////////////////
static int nextpid = 1;
static pagetable_t proc_pagetable(struct proc*);
static void proc_free_pagetable(pagetable_t pagetable, uint64 sz);
static void proc_freewalk(pagetable_t pagetable);
static uint64 proc_shrink(pagetable_t pagetable, uint64 oldsz, uint64 newsz);
static int proc_loadseg(pagetable_t pagetable, uint64 va, void *bin, uint offset, uint sz);
static void proc_guard(pagetable_t pagetable, uint64 va);


////////////////////////////////////////////////////////////////////////////////
// Global Definitions
////////////////////////////////////////////////////////////////////////////////
struct cpu cpu;
struct proc proc[NPROC];


////////////////////////////////////////////////////////////////////////////////
// Process API Functions 
////////////////////////////////////////////////////////////////////////////////


void proc_init(void) {

    for(int i = 0; i < NPROC; i++) {

        void *pa;

        proc[i].state = UNUSED;
        proc[i].kstack = KSTACK(i);
        pa = vm_page_alloc();

        if(pa == 0) panic("proc_init");
        if(vm_page_insert(kernel_pagetable, proc[i].kstack, (uint64)pa, PTE_R | PTE_W) < 0) panic("proc_init");
    }
}


struct proc* proc_load_user_init(void) {

    void *bin = &_binary_user_init_start;
    struct proc *p = 0x00;

    p = proc_alloc();

    if(p == 0) panic("proc_load_user_init");
    if(proc_load_elf(p, bin) < 0) panic("proc_load_user_init");

    return p;
}


struct proc* proc_alloc(void) {

    for(int i = 0; i < NPROC; i++) {

        struct proc *p = &proc[i];

        if(p->state != UNUSED) continue;

        p->pid = nextpid++;
        p->state = USED;
        p->wait_read = 0;
        p->wait_write = 0;
        p->sz = 0;

        p->trapframe = (struct trapframe *)vm_page_alloc();

        if(p->trapframe == 0) {
            proc_free(p);
            return 0;
        }

        memset(p->trapframe, 0, PGSIZE);

        p->pagetable = proc_pagetable(p);

        if(p->pagetable == 0) {
            proc_free(p);
            return 0;
        }

        memset(&p->context, 0, sizeof(p->context));
        p->context.ra = (uint64)usertrapret;
        p->context.sp = p->kstack + PGSIZE;
        return p;
    } 

    return 0;
}

void proc_free(struct proc *p) {

    if(p->trapframe) vm_page_free((void*)p->trapframe);

    p->trapframe = 0;
    if(p->pagetable) proc_free_pagetable(p->pagetable, p->sz);

    p->pagetable = 0;
    p->sz = 0;
    p->pid = 0;
    p->wait_read = 0;
    p->wait_write = 0;

    memset(&p->context, 0, sizeof(p->context));
    p->state = UNUSED;
}

int proc_load_elf(struct proc *p, void *bin) {

    struct elfhdr elf;
    struct proghdr ph;
    int i, off;
    uint64 sz=0, sp=0;
    pagetable_t pagetable=0;

    elf = *(struct elfhdr*) bin;

    if(elf.magic != ELF_MAGIC) goto bad;

    if((pagetable = proc_pagetable(p)) == 0) goto bad;

    for(i = 0, off = elf.phoff; i < elf.phnum; i++, off += sizeof(ph)) {

        uint64 sz1;
        int perm;

        ph = *(struct proghdr*)((char*)bin + off);

        if(ph.type != ELF_PROG_LOAD) continue;
        if(ph.memsz < ph.filesz) goto bad;
        if(ph.vaddr + ph.memsz < ph.vaddr) goto bad;
        if(ph.vaddr % PGSIZE != 0) goto bad;

        sz1 = proc_resize(pagetable, sz, ph.vaddr + ph.memsz);

        if(sz1 == 0)  goto bad;
        sz = sz1;

        if(proc_loadseg(pagetable, ph.vaddr, bin, ph.off, ph.filesz) < 0) goto bad;

        perm = PTE_U;
        if(ph.flags & ELF_PROG_FLAG_READ) perm |= PTE_R;
        if(ph.flags & ELF_PROG_FLAG_WRITE) perm |= PTE_W;
        if(ph.flags & ELF_PROG_FLAG_EXEC) perm |= PTE_X;

        for(uint64 va = ph.vaddr; va < ph.vaddr + ph.memsz; va += PGSIZE) {

            pte_t *pte = walk_pgtable(pagetable, va, 0);
            if(pte == 0 || (*pte & PTE_V) == 0) goto bad;
            *pte = PA2PTE(PTE2PA(*pte)) | perm | PTE_V;
        }
    }

    sz = PGROUNDUP(sz);
    if((sz = proc_resize(pagetable, sz, sz + 2 * PGSIZE)) == 0) goto bad;
    proc_guard(pagetable, sz - 2 * PGSIZE);
    sp = sz;
    sp -= sp % 16;

    proc_free_pagetable(p->pagetable, p->sz);
    p->pagetable = pagetable;
    p->sz = sz;
    p->trapframe->epc = elf.entry;
    p->trapframe->sp = sp;
    p->state = RUNNABLE;
    return 0;

bad:
    if(pagetable) proc_free_pagetable(pagetable, sz);
    return -1;
}


uint64 proc_resize(pagetable_t pagetable, uint64 oldsz, uint64 newsz) {

    uint64 oldend, newend;

    if(newsz > TRAPFRAME) return 0;
    if(newsz < oldsz) return proc_shrink(pagetable, oldsz, newsz);

    oldend = PGROUNDUP(oldsz);
    newend = PGROUNDUP(newsz);
    if(newend > oldend) {
        if(vm_map_range(pagetable, oldend, newend - oldend, PTE_R | PTE_W | PTE_U) < 0) return 0;
    }
    return newsz;
}

int proc_vmcopy(pagetable_t old, pagetable_t new, uint64 sz) {

  pte_t *pte;
  uint64 pa, i;
  uint flags;
  void *mem;

  for(i = 0; i < sz; i += PGSIZE) {

    if((pte = walk_pgtable(old, i, 0)) == 0) continue;
    if((*pte & PTE_V) == 0) continue;

    pa = PTE2PA(*pte);
    flags = PTE_FLAGS(*pte);
    if((mem = vm_page_alloc()) == 0) goto err;

    memmove(mem, (char*)pa, PGSIZE);
    if(vm_page_insert(new, i, (uint64)mem, flags) != 0) {
      vm_page_free(mem);
      goto err;
    }
  }

  return 0;

 err:
  vm_page_remove(new, 0, i / PGSIZE, 1);
  return -1;
}


////////////////////////////////////////////////////////////////////////////////
// Static Helper Functions
////////////////////////////////////////////////////////////////////////////////

static pagetable_t proc_pagetable(struct proc *p) {

    pagetable_t pagetable;

    pagetable = vm_create_pagetable();
    if(pagetable == 0) return 0;

    if(vm_page_insert(pagetable, TRAMPOLINE, (uint64)trampoline, PTE_R | PTE_X) < 0) goto bad;
    if(vm_page_insert(pagetable, TRAPFRAME, (uint64)p->trapframe, PTE_R | PTE_W) < 0) {
        vm_page_remove(pagetable, TRAMPOLINE, 1, 0);
        goto bad;
    }

    return pagetable;

bad:
    proc_freewalk(pagetable);
    return 0;
}

static void proc_free_pagetable(pagetable_t pagetable, uint64 sz) {

    vm_page_remove(pagetable, TRAMPOLINE, 1, 0);
    vm_page_remove(pagetable, TRAPFRAME, 1, 0);
    if(sz > 0) vm_page_remove(pagetable, 0, PGROUNDUP(sz) / PGSIZE, 1);
    proc_freewalk(pagetable);

}

static void proc_freewalk(pagetable_t pagetable) {

  // there are 2^9 = 512 PTEs in a page table.
  for(int i = 0; i < 512; i++) {

    pte_t pte = pagetable[i];
    if((pte & PTE_V) && (pte & (PTE_R|PTE_W|PTE_X)) == 0) {
      uint64 child = PTE2PA(pte);
      proc_freewalk((pagetable_t)child);
      pagetable[i] = 0;
    } else if(pte & PTE_V) {
      panic("freewalk: leaf");
    }
  }
  vm_page_free((void*)pagetable);
}

static uint64 proc_shrink(pagetable_t pagetable, uint64 oldsz, uint64 newsz) {

  if(newsz >= oldsz) return oldsz;

  if(PGROUNDUP(newsz) < PGROUNDUP(oldsz)) {
    int npages = (PGROUNDUP(oldsz) - PGROUNDUP(newsz)) / PGSIZE;
    vm_page_remove(pagetable, PGROUNDUP(newsz), npages, 1);
  }

  return newsz;
}

static int proc_loadseg(pagetable_t pagetable, uint64 va, void *bin, uint offset, uint sz) {

  uint i, n;
  uint64 pa;

  for(i = 0; i < sz; i += PGSIZE) {

    pa = vm_lookup(pagetable, va + i);

    if(pa == 0) panic("proc_loadseg");
    if(sz - i < PGSIZE) {
      n = sz - i;
    } else {
      n = PGSIZE;
    }
    memmove((void*)pa, (char*)bin + offset + i, n);
  }

  return 0;

}

static void proc_guard(pagetable_t pagetable, uint64 va) {

    pte_t *pte;

    pte = walk_pgtable(pagetable, va, 0);
    if(pte == 0) panic("proc_guard");

    *pte &= ~PTE_U;
}

struct proc *proc_find(int pid) {

  for(int i=0; i<NPROC; i++) {
    if(proc[i].pid == pid) return &proc[i];
  } 

  return 0;

}
