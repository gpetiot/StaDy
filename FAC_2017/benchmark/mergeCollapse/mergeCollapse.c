#define stackLen 5

/* Declaration of the stack of ordered subsequence (called 'run' in the paper)
 * lengths. The size of this stack is limited to 5 run lengths. This size allows
 * to sort arrays of maximal size of 160. The stack is a global variable.
 * Its size is stackSize. */

int* runLen; /* Stack of run lengths.
 For example runLen = {120, 80, 25, 20} with stackSize = 4.
 Each value is the size of an ordered subsequence. */
int stackSize; /* Stack size between 0 and 5. StackSize = n means
 the valid subsequences are between 0 and n-1 in runLen. */

/* 1 mergeAt function. Its parameter n is the position
   of the run to merge with the next in position n+1 */
   
/*@
  requires 1 <= n+1 < stackSize <= stackLen;
  requires n == stackSize - 2 || n == stackSize - 3;
  requires \valid(runLen+(0..4));
  assigns stackSize, runLen[n..4];
  ensures stackSize == \old(stackSize) - 1;
  ensures runLen[n] == \old(runLen[n]) + \old(runLen[n+1]);
  ensures n == \old(stackSize)-3 ==> runLen[n+1] == \old(runLen[n+2]);
*/
void mergeAt(int n) {
  int i;

  int len1 = runLen[n];
  int len2 = runLen[n + 1];

  /* merge the 2 runs in  position n and n+1 */
  runLen[n] = len1 + len2;
  {
     if (n == stackSize - 3) {
       runLen[n + 1] = runLen[n + 2];
    }
  }
  stackSize--;
}


/*  initial mergeCollapse function containing a bug.Its code is in listing3. 
   It must modify the stack
   merging the adjacent runs until the following main post condition be established again:
   forall  i in 1 to stackSize-2 :
   1. forall i in 0 to� stackSize-2: runLen[i]>runLen[i+1]
   2. forall i in 1 to� stackSize-2: runLen[i-1]>runLen[i]+runLen[i+1].
   For example : 120, 80, 25, 20 where stackSize=4.
   It is called in the main loop of TimSort.
   At each times TimSort add a run on the stack,
   that can breaks the invariant. Example 120, 80, 25, 20, 30 where stackSize=5
   After mergeCollapse execution the stack is: 120, 80, 45, 30 where stackSize=4.
   The invariant is broken because 120<80+45. This is a bug, then a counter example*/
/* The proof of the post conditions e2 and e3 fails */

/* The contract is that in listing 9 completed by */
/* The preconditions 4 to 8 adapt the class invariant of listing 7*/
/* To use PathCrawler, we inlined the four auxiliary predicates that are in the table in page 9 in the paper */

/*@
  requires \valid(runLen+(0..4));
  requires 0 < stackSize;
  requires stackSize <= stackLen; // WARNING: requires stackSize <= 4; is not in [GoRdB+15]!

  requires \forall integer i; 0 <= i < stackSize ==> runLen[i] <= 500; // to avoid overflows

  requires \forall integer i; 0 <= i < stackSize-4 ==>
     (
      (0 <= i && i+2 < stackLen ==> runLen[i] > runLen[i+1] + runLen[i+2]) &&
      (0 <= i && i+1 < stackLen ==> runLen[i] > runLen[i+1]) &&
      (0 <= i < stackLen ==> runLen[i] >= 16)
     );
  requires (0 <= stackSize-4 && stackSize-4+1 < stackLen) ==> runLen[stackSize-4] > runLen[stackSize-4+1];
  requires 0 <= stackSize-3 < stackLen ==> runLen[stackSize-3] >= 16;
  requires 0 <= stackSize-2 < stackLen ==> runLen[stackSize-2] >= 16;
  requires 0 <= stackSize-1 < stackLen ==> runLen[stackSize-1] >= 1;

  requires
     (
      ((0 <= stackSize-4 && stackSize-4+2 < stackLen) ==> runLen[stackSize-4] > runLen[stackSize-4+1] + runLen[stackSize-4+2]) &&
      ((0 <= stackSize-4 && stackSize-4+1 < stackLen) ==> runLen[stackSize-4] > runLen[stackSize-4+1]) &&
      (0 <= stackSize-4 < stackLen ==> runLen[stackSize-4] >= 16)
     );
  requires ((0 <= stackSize-3 && stackSize-3+1 < stackLen) ==> runLen[stackSize-3] > runLen[stackSize-3+1]);
  assigns stackSize, runLen[0..4];
  ensures stackSize <= \old(stackSize);
  ensures e2: \forall integer i; 0 <= i < stackSize-3 ==>
     (
      (0 <= i && i+2 < stackLen ==> runLen[i] > runLen[i+1] + runLen[i+2]) &&
      (0 <= i && i+1 < stackLen ==> runLen[i] > runLen[i+1]) &&
      (0 <= i < stackLen ==> runLen[i] >= 16)
     );
  ensures e3: \forall integer i; 0 <= i < stackSize-2 ==>
     (
      (0 <= i && i+2 < stackLen ==> runLen[i] > runLen[i+1] + runLen[i+2]) &&
      (0 <= i && i+1 < stackLen ==> runLen[i] > runLen[i+1])
     );
*/
void mergeCollapse() {
  int n = stackSize - 2;
	/* merge the 2 runs in the top of the stack */
  /*@
    loop invariant -2 < n <= 3;
    loop invariant 0 < stackSize <= stackLen;
    loop invariant \forall integer i; 0 <= i < stackSize-4 ==>
     (
      ((0 <= i && i+2 < stackLen) ==> runLen[i] > runLen[i+1] + runLen[i+2]) &&
      ((0 <= i && i+1 < stackLen) ==> runLen[i] > runLen[i+1]) &&
      (0 <= i < stackLen ==> runLen[i] >= 16)
     );
    loop invariant (0 <= stackSize-4 && stackSize-4+1 < stackLen) ==> runLen[stackSize-4] > runLen[stackSize-4+1];
    loop invariant 0 <= stackSize-3 < stackLen ==> runLen[stackSize-3] >= 16;
    loop invariant 0 <= stackSize-2 < stackLen ==> runLen[stackSize-2] >= 16;
    loop invariant 0 <= stackSize-1 < stackLen ==> runLen[stackSize-1] >= 1;
    loop invariant runLen[stackSize-1] >= \at(runLen[stackSize-1], Pre);
    loop invariant stackSize <= \at(stackSize, Pre);
    loop assigns n, stackSize, runLen[0..4];
    loop variant stackSize;
  */
  while(stackSize > 1) {
    n = stackSize - 2;
    if (n > 0 && runLen[n-1] <= runLen[n] + runLen[n+1]) {
      if(runLen[n-1] < runLen[n+1])
        n--;
      mergeAt(n); /* merge the 2 runs in position n and n+1 */
    } else if (runLen[n] <= runLen[n+1]) {
      mergeAt(n);
    } else {
      break; /* Here the post condition e2 and e3 should be establish. That is not the case  */
    }
  }
}

/*  fixed mergeCollapse function called newMergeCollapse (code in listing 6) .
  Its contract is the same as the previous one. In contrast its code is corrected 
   as in listing 6 */

/*@
  requires \valid(runLen+(0..4));
  requires 0 < stackSize;
  requires stackSize <= stackLen; // WARNING: requires stackSize <= 4; is not in [GoRdB+15]!

  requires \forall integer i; 0 <= i < stackSize ==> runLen[i] <= 500; // to avoid overflows

  requires \forall integer i; 0 <= i < stackSize-4 ==>
     (
      (0 <= i && i+2 < stackLen ==> runLen[i] > runLen[i+1] + runLen[i+2]) &&
      (0 <= i && i+1 < stackLen ==> runLen[i] > runLen[i+1]) &&
      (0 <= i < stackLen ==> runLen[i] >= 16)
     );
  requires (0 <= stackSize-4 && stackSize-4+1 < stackLen) ==> runLen[stackSize-4] > runLen[stackSize-4+1];
  requires 0 <= stackSize-3 < stackLen ==> runLen[stackSize-3] >= 16;
  requires 0 <= stackSize-2 < stackLen ==> runLen[stackSize-2] >= 16;
  requires 0 <= stackSize-1 < stackLen ==> runLen[stackSize-1] >= 1;

  requires
     (
      ((0 <= stackSize-4 && stackSize-4+2 < stackLen) ==> runLen[stackSize-4] > runLen[stackSize-4+1] + runLen[stackSize-4+2]) &&
      ((0 <= stackSize-4 && stackSize-4+1 < stackLen) ==> runLen[stackSize-4] > runLen[stackSize-4+1]) &&
      (0 <= stackSize-4 < stackLen ==> runLen[stackSize-4] >= 16)
     );
  requires ((0 <= stackSize-3 && stackSize-3+1 < stackLen) ==> runLen[stackSize-3] > runLen[stackSize-3+1]);
  assigns stackSize, runLen[0..4];
  ensures stackSize <= \old(stackSize);
  ensures \forall integer i; 0 <= i < stackSize-3 ==>
     (
      (0 <= i && i+2 < stackLen ==> runLen[i] > runLen[i+1] + runLen[i+2]) &&
      (0 <= i && i+1 < stackLen ==> runLen[i] > runLen[i+1]) &&
      (0 <= i < stackLen ==> runLen[i] >= 16)
     );
  ensures \forall integer i; 0 <= i < stackSize-2 ==>
     (
      (0 <= i && i+2 < stackLen ==> runLen[i] > runLen[i+1] + runLen[i+2]) &&
      (0 <= i && i+1 < stackLen ==> runLen[i] > runLen[i+1])
     );
*/
void newMergeCollapse() {
  int n = stackSize - 2;
  /*@
    loop invariant -2 < n <= 3;
    loop invariant 0 < stackSize <= stackLen;
    loop invariant \forall integer i; 0 <= i < stackSize-4 ==>
     (
      ((0 <= i && i+2 < stackLen) ==> runLen[i] > runLen[i+1] + runLen[i+2]) &&
      ((0 <= i && i+1 < stackLen) ==> runLen[i] > runLen[i+1]) &&
      (0 <= i < stackLen ==> runLen[i] >= 16)
     );
    loop invariant (0 <= stackSize-4 && stackSize-4+1 < stackLen) ==> runLen[stackSize-4] > runLen[stackSize-4+1];
    loop invariant 0 <= stackSize-3 < stackLen ==> runLen[stackSize-3] >= 16;
    loop invariant 0 <= stackSize-2 < stackLen ==> runLen[stackSize-2] >= 16;
    loop invariant 0 <= stackSize-1 < stackLen ==> runLen[stackSize-1] >= 1;
    loop invariant runLen[stackSize-1] >= \at(runLen[stackSize-1], Pre);
    loop invariant stackSize <= \at(stackSize, Pre);
    loop assigns n, stackSize, runLen[0..4];
    loop variant stackSize;
  */
  while(stackSize > 1) {
    n = stackSize - 2;
    if(     n > 0 && runLen[n-1] <= runLen[n] + runLen[n+1]
       || n-1 > 0 && runLen[n-2] <= runLen[n] + runLen[n-1]) {
      if(runLen[n-1] < runLen[n+1])
        n--;
    } else if(n < 0 || runLen[n] > runLen[n+1]) {
        break; // Invariant is established
    }
    mergeAt(n);
  }
}
