import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2368 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw2368step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical2368 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2368 = injectiveMoment H node1844 := by
  calc
    injectiveMoment H raw2368 = injectiveMoment H raw2368step0 := by
      have heq : raw2368step0 = (fun i j => raw2368 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2368 permutation33 permutation10
    _ = injectiveMoment H node1844 := by rfl

def raw2369 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw2369step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical2369 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2369 = injectiveMoment H node2452 := by
  calc
    injectiveMoment H raw2369 = injectiveMoment H raw2369step0 := by
      have heq : raw2369step0 = (fun i j => raw2369 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2369 permutation36 permutation15
    _ = injectiveMoment H node2452 := by rfl

def raw2370 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -2, 0]]

theorem canonical2370 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2370 = injectiveMoment H node1812 := by
  rfl

def raw2371 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -3, 1]]

theorem canonical2371 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2371 = injectiveMoment H node1813 := by
  rfl

def raw2372 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, -1, 0]]

def raw2372step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical2372 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2372 = injectiveMoment H node2451 := by
  calc
    injectiveMoment H raw2372 = injectiveMoment H raw2372step0 := by
      have heq : raw2372step0 = (fun i j => raw2372 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2372 permutation36 permutation15
    _ = injectiveMoment H node2451 := by rfl

def raw2373 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, -3, 1]]

def raw2373step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, 0, 0, -1]]

theorem canonical2373 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2373 = injectiveMoment H node843 := by
  calc
    injectiveMoment H raw2373 = injectiveMoment H raw2373step0 := by
      have heq : raw2373step0 = (fun i j => raw2373 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2373 permutation10 permutation15
    _ = injectiveMoment H node843 := by rfl

def raw2374 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical2374 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2374 = injectiveMoment H node1814 := by
  rfl

def raw2375 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, -1, 0, -1]]

def raw2375step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![1, 2, -3, 0], ![2, -2, 1, -1]]

def raw2375step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -3, 1]]

theorem canonical2375 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2375 = injectiveMoment H node504 := by
  calc
    injectiveMoment H raw2375 = injectiveMoment H raw2375step0 := by
      have heq : raw2375step0 = raw2375.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2375).symm
    injectiveMoment H raw2375step0 = injectiveMoment H raw2375step1 := by
      have heq : raw2375step1 = (fun i j => raw2375step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2375step0 permutation29 permutation20
    _ = injectiveMoment H node504 := by rfl

def raw2376 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical2376 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2376 = injectiveMoment H node1815 := by
  rfl

def raw2377 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2377step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical2377 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2377 = injectiveMoment H node1845 := by
  calc
    injectiveMoment H raw2377 = injectiveMoment H raw2377step0 := by
      have heq : raw2377step0 = (fun i j => raw2377 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2377 permutation33 permutation10
    _ = injectiveMoment H node1845 := by rfl

def raw2378 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, -1, 0]]

def raw2378step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 0, -1]]

theorem canonical2378 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2378 = injectiveMoment H node523 := by
  calc
    injectiveMoment H raw2378 = injectiveMoment H raw2378step0 := by
      have heq : raw2378step0 = (fun i j => raw2378 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2378 permutation9 permutation10
    _ = injectiveMoment H node523 := by rfl

def raw2379 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical2379 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2379 = injectiveMoment H node1816 := by
  rfl

def raw2380 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, -2, 1]]

theorem canonical2380 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2380 = injectiveMoment H node507 := by
  rfl

def raw2381 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -2, -1]]

theorem canonical2381 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2381 = injectiveMoment H node508 := by
  rfl

def raw2382 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -3, 0]]

def raw2382step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![1, 2, 0, -3], ![2, -2, 0, 0]]

def raw2382step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical2382 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2382 = injectiveMoment H node1235 := by
  calc
    injectiveMoment H raw2382 = injectiveMoment H raw2382step0 := by
      have heq : raw2382step0 = raw2382.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2382).symm
    injectiveMoment H raw2382step0 = injectiveMoment H raw2382step1 := by
      have heq : raw2382step1 = (fun i j => raw2382step0 (permutation20 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2382step0 permutation20 permutation23
    _ = injectiveMoment H node1235 := by rfl

def raw2383 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, 0, -2, 1], ![1, 1, -1, -1]]

def raw2383step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

theorem canonical2383 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2383 = injectiveMoment H node842 := by
  calc
    injectiveMoment H raw2383 = injectiveMoment H raw2383step0 := by
      have heq : raw2383step0 = (fun i j => raw2383 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2383 permutation9 permutation15
    _ = injectiveMoment H node842 := by rfl

def raw2384 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 1, -2, 0]]

def raw2384step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 0, -2]]

theorem canonical2384 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2384 = injectiveMoment H node853 := by
  calc
    injectiveMoment H raw2384 = injectiveMoment H raw2384step0 := by
      have heq : raw2384step0 = (fun i j => raw2384 (permutation9 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2384 permutation9 permutation16
    _ = injectiveMoment H node853 := by rfl

def raw2385 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, -3, 1]]

def raw2385step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![1, 2, 0, -3], ![2, -2, -1, 1]]

def raw2385step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

theorem canonical2385 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2385 = injectiveMoment H node839 := by
  calc
    injectiveMoment H raw2385 = injectiveMoment H raw2385step0 := by
      have heq : raw2385step0 = raw2385.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2385).symm
    injectiveMoment H raw2385step0 = injectiveMoment H raw2385step1 := by
      have heq : raw2385step1 = (fun i j => raw2385step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2385step0 permutation30 permutation24
    _ = injectiveMoment H node839 := by rfl

def raw2386 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, 1, -3, 1], ![1, 0, 0, -1]]

def raw2386step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 1, 0], ![1, 2, -3, 0], ![2, -2, 1, -1]]

def raw2386step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

theorem canonical2386 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2386 = injectiveMoment H node839 := by
  calc
    injectiveMoment H raw2386 = injectiveMoment H raw2386step0 := by
      have heq : raw2386step0 = raw2386.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2386).symm
    injectiveMoment H raw2386step0 = injectiveMoment H raw2386step1 := by
      have heq : raw2386step1 = (fun i j => raw2386step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2386step0 permutation30 permutation30
    _ = injectiveMoment H node839 := by rfl

def raw2387 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, 2, -2, -1], ![1, -1, -1, 1]]

def raw2387step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -2, -1]]

theorem canonical2387 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2387 = injectiveMoment H node508 := by
  calc
    injectiveMoment H raw2387 = injectiveMoment H raw2387step0 := by
      have heq : raw2387step0 = (fun i j => raw2387 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2387 permutation10 permutation9
    _ = injectiveMoment H node508 := by rfl

def raw2388 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw2388step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, -3, 0, 2], ![2, 2, 0, -4]]

def raw2388step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 2, 2, -4], ![1, -2, 0, 1]]

theorem canonical2388 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2388 = injectiveMoment H node1125 := by
  calc
    injectiveMoment H raw2388 = injectiveMoment H raw2388step0 := by
      have heq : raw2388step0 = raw2388.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2388).symm
    injectiveMoment H raw2388step0 = injectiveMoment H raw2388step1 := by
      have heq : raw2388step1 = (fun i j => raw2388step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2388step0 permutation18 permutation21
    _ = injectiveMoment H node1125 := by rfl

def raw2389 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 1, 1, -3]]

theorem canonical2389 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2389 = injectiveMoment H node509 := by
  rfl

def raw2390 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2390step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

theorem canonical2390 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2390 = injectiveMoment H node2450 := by
  calc
    injectiveMoment H raw2390 = injectiveMoment H raw2390step0 := by
      have heq : raw2390step0 = (fun i j => raw2390 (permutation42 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2390 permutation42 permutation15
    _ = injectiveMoment H node2450 := by rfl

def raw2391 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 0, 1, -1], ![2, 0, 0, -2]]

def raw2391step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical2391 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2391 = injectiveMoment H node840 := by
  calc
    injectiveMoment H raw2391 = injectiveMoment H raw2391step0 := by
      have heq : raw2391step0 = (fun i j => raw2391 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2391 permutation12 permutation15
    _ = injectiveMoment H node840 := by rfl

def raw2392 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

theorem canonical2392 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2392 = injectiveMoment H node1817 := by
  rfl

def raw2393 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw2393step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, -2, -1, 2], ![2, 1, 0, -3]]

def raw2393step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical2393 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2393 = injectiveMoment H node829 := by
  calc
    injectiveMoment H raw2393 = injectiveMoment H raw2393step0 := by
      have heq : raw2393step0 = raw2393.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2393).symm
    injectiveMoment H raw2393step0 = injectiveMoment H raw2393step1 := by
      have heq : raw2393step1 = (fun i j => raw2393step0 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2393step0 permutation22 permutation23
    _ = injectiveMoment H node829 := by rfl

def raw2394 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical2394 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2394 = injectiveMoment H node1818 := by
  rfl

def raw2395 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical2395 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2395 = injectiveMoment H node1819 := by
  rfl

def raw2396 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 1, -1]]

def raw2396step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical2396 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2396 = injectiveMoment H node1819 := by
  calc
    injectiveMoment H raw2396 = injectiveMoment H raw2396step0 := by
      have heq : raw2396step0 = (fun i j => raw2396 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2396 permutation34 permutation9
    _ = injectiveMoment H node1819 := by rfl

def raw2397 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw2397step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, -2, 0, 1], ![2, 1, -1, -2]]

def raw2397step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![-1, 2, 0, -1], ![-2, -1, 1, 2]]

def raw2397step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 2, -2]]

theorem canonical2397 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2397 = injectiveMoment H node1111 := by
  calc
    injectiveMoment H raw2397 = injectiveMoment H raw2397step0 := by
      have heq : raw2397step0 = raw2397.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2397).symm
    injectiveMoment H raw2397step0 = injectiveMoment H raw2397step1 := by
      have heq : raw2397step1 = -raw2397step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2397step0).symm
    injectiveMoment H raw2397step1 = injectiveMoment H raw2397step2 := by
      have heq : raw2397step2 = (fun i j => raw2397step1 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2397step1 permutation15 permutation24
    _ = injectiveMoment H node1111 := by rfl

def raw2398 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical2398 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2398 = injectiveMoment H node1820 := by
  rfl

def raw2399 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem canonical2399 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2399 = injectiveMoment H node510 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
