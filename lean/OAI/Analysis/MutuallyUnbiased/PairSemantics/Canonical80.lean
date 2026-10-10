import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2560 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw2560step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![2, -2, 0, 0], ![1, 2, 0, -3]]

def raw2560step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical2560 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2560 = injectiveMoment H node1235 := by
  calc
    injectiveMoment H raw2560 = injectiveMoment H raw2560step0 := by
      have heq : raw2560step0 = raw2560.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2560).symm
    injectiveMoment H raw2560step0 = injectiveMoment H raw2560step1 := by
      have heq : raw2560step1 = (fun i j => raw2560step0 (permutation18 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2560step0 permutation18 permutation23
    _ = injectiveMoment H node1235 := by rfl

def raw2561 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw2561step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 0, -2]]

theorem canonical2561 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2561 = injectiveMoment H node853 := by
  calc
    injectiveMoment H raw2561 = injectiveMoment H raw2561step0 := by
      have heq : raw2561step0 = (fun i j => raw2561 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2561 permutation9 permutation15
    _ = injectiveMoment H node853 := by rfl

def raw2562 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![1, 1, 0, -2], ![1, 0, 0, -1]]

def raw2562step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 0, -2]]

theorem canonical2562 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2562 = injectiveMoment H node853 := by
  calc
    injectiveMoment H raw2562 = injectiveMoment H raw2562step0 := by
      have heq : raw2562step0 = (fun i j => raw2562 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2562 permutation10 permutation15
    _ = injectiveMoment H node853 := by rfl

def raw2563 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw2563step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

theorem canonical2563 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2563 = injectiveMoment H node1832 := by
  calc
    injectiveMoment H raw2563 = injectiveMoment H raw2563step0 := by
      have heq : raw2563step0 = (fun i j => raw2563 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2563 permutation39 permutation9
    _ = injectiveMoment H node1832 := by rfl

def raw2564 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw2564step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical2564 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2564 = injectiveMoment H node2455 := by
  calc
    injectiveMoment H raw2564 = injectiveMoment H raw2564step0 := by
      have heq : raw2564step0 = (fun i j => raw2564 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2564 permutation34 permutation15
    _ = injectiveMoment H node2455 := by rfl

def raw2565 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, -1, 0, -1]]

theorem canonical2565 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2565 = injectiveMoment H node1846 := by
  rfl

def raw2566 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw2566step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

theorem canonical2566 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2566 = injectiveMoment H node2454 := by
  calc
    injectiveMoment H raw2566 = injectiveMoment H raw2566step0 := by
      have heq : raw2566step0 = (fun i j => raw2566 (permutation33 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2566 permutation33 permutation15
    _ = injectiveMoment H node2454 := by rfl

def raw2567 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw2567step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 0, 1, 0], ![2, -1, 0, 0, -1], ![1, 1, 0, -1, -1]]

def raw2567step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![2, -1, 0, -1], ![1, 1, -1, -1]]

def raw2567step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

theorem canonical2567 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2567 = injectiveMoment H node1265 := by
  calc
    injectiveMoment H raw2567 = injectiveMoment H raw2567step0 := by
      have heq : raw2567step0 = raw2567.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2567).symm
    injectiveMoment H raw2567step0 = injectiveMoment H raw2567step1 := by
      have hz : ∀ i, raw2567step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw2567step1 = (fun i j => raw2567step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2567step0 permutation80 hz
    injectiveMoment H raw2567step1 = injectiveMoment H raw2567step2 := by
      have heq : raw2567step2 = (fun i j => raw2567step1 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2567step1 permutation21 permutation18
    _ = injectiveMoment H node1265 := by rfl

def raw2568 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw2568step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 0, 0, 1], ![2, -1, 0, -1, 0], ![1, 1, 0, 0, -2]]

def raw2568step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![2, -1, -1, 0], ![1, 1, 0, -2]]

def raw2568step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical2568 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2568 = injectiveMoment H node1047 := by
  calc
    injectiveMoment H raw2568 = injectiveMoment H raw2568step0 := by
      have heq : raw2568step0 = raw2568.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2568).symm
    injectiveMoment H raw2568step0 = injectiveMoment H raw2568step1 := by
      have hz : ∀ i, raw2568step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw2568step1 = (fun i j => raw2568step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2568step0 permutation80 hz
    injectiveMoment H raw2568step1 = injectiveMoment H raw2568step2 := by
      have heq : raw2568step2 = (fun i j => raw2568step1 (permutation24 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2568step1 permutation24 permutation24
    _ = injectiveMoment H node1047 := by rfl

def raw2569 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![2, 0, 0, -2]]

def raw2569step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 1, 0, 0], ![2, -1, -1, 0, 0], ![1, 1, 0, 0, -2]]

def raw2569step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![2, -1, -1, 0], ![1, 1, 0, -2]]

def raw2569step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical2569 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2569 = injectiveMoment H node1053 := by
  calc
    injectiveMoment H raw2569 = injectiveMoment H raw2569step0 := by
      have heq : raw2569step0 = raw2569.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2569).symm
    injectiveMoment H raw2569step0 = injectiveMoment H raw2569step1 := by
      have hz : ∀ i, raw2569step0 i (permutation104 0) = 0 := by decide +kernel
      have heq : raw2569step1 = (fun i j => raw2569step0 i (permutation104 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2569step0 permutation104 hz
    injectiveMoment H raw2569step1 = injectiveMoment H raw2569step2 := by
      have heq : raw2569step2 = (fun i j => raw2569step1 (permutation22 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2569step1 permutation22 permutation24
    _ = injectiveMoment H node1053 := by rfl

def raw2570 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2570step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical2570 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2570 = injectiveMoment H node1786 := by
  calc
    injectiveMoment H raw2570 = injectiveMoment H raw2570step0 := by
      have heq : raw2570step0 = (fun i j => raw2570 (permutation35 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2570 permutation35 permutation10
    _ = injectiveMoment H node1786 := by rfl

def raw2571 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw2571step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical2571 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2571 = injectiveMoment H node1793 := by
  calc
    injectiveMoment H raw2571 = injectiveMoment H raw2571step0 := by
      have heq : raw2571step0 = (fun i j => raw2571 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2571 permutation33 permutation10
    _ = injectiveMoment H node1793 := by rfl

def raw2572 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2572step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical2572 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2572 = injectiveMoment H node2448 := by
  calc
    injectiveMoment H raw2572 = injectiveMoment H raw2572step0 := by
      have heq : raw2572step0 = (fun i j => raw2572 (permutation36 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2572 permutation36 permutation16
    _ = injectiveMoment H node2448 := by rfl

def raw2573 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw2573step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![2, -1, -1, 0], ![1, 1, 0, -2]]

def raw2573step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical2573 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2573 = injectiveMoment H node1053 := by
  calc
    injectiveMoment H raw2573 = injectiveMoment H raw2573step0 := by
      have heq : raw2573step0 = raw2573.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2573).symm
    injectiveMoment H raw2573step0 = injectiveMoment H raw2573step1 := by
      have heq : raw2573step1 = (fun i j => raw2573step0 (permutation22 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2573step0 permutation22 permutation24
    _ = injectiveMoment H node1053 := by rfl

def raw2574 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 0, 0, 0], ![2, 0, -1, -1]]

def raw2574step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 1, 0, 0], ![2, -1, 0, 0, -1], ![1, 1, -1, 0, -1]]

def raw2574step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![2, -1, 0, -1], ![1, 1, -1, -1]]

def raw2574step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

theorem canonical2574 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2574 = injectiveMoment H node1265 := by
  calc
    injectiveMoment H raw2574 = injectiveMoment H raw2574step0 := by
      have heq : raw2574step0 = raw2574.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2574).symm
    injectiveMoment H raw2574step0 = injectiveMoment H raw2574step1 := by
      have hz : ∀ i, raw2574step0 i (permutation104 0) = 0 := by decide +kernel
      have heq : raw2574step1 = (fun i j => raw2574step0 i (permutation104 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2574step0 permutation104 hz
    injectiveMoment H raw2574step1 = injectiveMoment H raw2574step2 := by
      have heq : raw2574step2 = (fun i j => raw2574step1 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2574step1 permutation21 permutation18
    _ = injectiveMoment H node1265 := by rfl

def raw2575 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw2575step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem canonical2575 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2575 = injectiveMoment H node1785 := by
  calc
    injectiveMoment H raw2575 = injectiveMoment H raw2575step0 := by
      have heq : raw2575step0 = (fun i j => raw2575 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2575 permutation33 permutation10
    _ = injectiveMoment H node1785 := by rfl

def raw2576 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem canonical2576 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2576 = injectiveMoment H node1847 := by
  rfl

def raw2577 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2577step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical2577 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2577 = injectiveMoment H node2449 := by
  calc
    injectiveMoment H raw2577 = injectiveMoment H raw2577step0 := by
      have heq : raw2577step0 = (fun i j => raw2577 (permutation38 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2577 permutation38 permutation16
    _ = injectiveMoment H node2449 := by rfl

def raw2578 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw2578step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![2, -1, 0, -1], ![1, 1, -1, -1]]

def raw2578step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

theorem canonical2578 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2578 = injectiveMoment H node1265 := by
  calc
    injectiveMoment H raw2578 = injectiveMoment H raw2578step0 := by
      have heq : raw2578step0 = raw2578.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2578).symm
    injectiveMoment H raw2578step0 = injectiveMoment H raw2578step1 := by
      have heq : raw2578step1 = (fun i j => raw2578step0 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2578step0 permutation21 permutation18
    _ = injectiveMoment H node1265 := by rfl

def raw2579 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2579step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -2, -1], ![0, 0, 1, -1], ![0, -2, 1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2579step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical2579 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2579 = injectiveMoment H node1793 := by
  calc
    injectiveMoment H raw2579 = injectiveMoment H raw2579step0 := by
      have heq : raw2579step0 = -raw2579 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2579).symm
    injectiveMoment H raw2579step0 = injectiveMoment H raw2579step1 := by
      have heq : raw2579step1 = (fun i j => raw2579step0 (permutation49 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2579step0 permutation49 permutation26
    _ = injectiveMoment H node1793 := by rfl

def raw2580 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, -1, 0, 0]]

def raw2580step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -2, -1], ![0, 0, 1, -1], ![0, -2, 1, 1], ![-1, 0, 0, 1], ![-1, 1, 0, 0]]

def raw2580step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical2580 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2580 = injectiveMoment H node1793 := by
  calc
    injectiveMoment H raw2580 = injectiveMoment H raw2580step0 := by
      have heq : raw2580step0 = -raw2580 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2580).symm
    injectiveMoment H raw2580step0 = injectiveMoment H raw2580step1 := by
      have heq : raw2580step1 = (fun i j => raw2580step0 (permutation55 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2580step0 permutation55 permutation26
    _ = injectiveMoment H node1793 := by rfl

def raw2581 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw2581step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![2, -1, -1, 0], ![1, 1, -1, -1]]

def raw2581step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical2581 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2581 = injectiveMoment H node1058 := by
  calc
    injectiveMoment H raw2581 = injectiveMoment H raw2581step0 := by
      have heq : raw2581step0 = raw2581.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2581).symm
    injectiveMoment H raw2581step0 = injectiveMoment H raw2581step1 := by
      have heq : raw2581step1 = (fun i j => raw2581step0 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2581step0 permutation21 permutation18
    _ = injectiveMoment H node1058 := by rfl

def raw2582 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical2582 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2582 = injectiveMoment H node1848 := by
  rfl

def raw2583 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2583step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical2583 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2583 = injectiveMoment H node1800 := by
  calc
    injectiveMoment H raw2583 = injectiveMoment H raw2583step0 := by
      have heq : raw2583step0 = (fun i j => raw2583 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2583 permutation33 permutation10
    _ = injectiveMoment H node1800 := by rfl

def raw2584 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw2584step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical2584 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2584 = injectiveMoment H node1800 := by
  calc
    injectiveMoment H raw2584 = injectiveMoment H raw2584step0 := by
      have heq : raw2584step0 = (fun i j => raw2584 (permutation34 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2584 permutation34 permutation10
    _ = injectiveMoment H node1800 := by rfl

def raw2585 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, -1, -1, 0]]

def raw2585step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![2, -1, 0, -1], ![1, 1, -2, 0]]

def raw2585step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical2585 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2585 = injectiveMoment H node1010 := by
  calc
    injectiveMoment H raw2585 = injectiveMoment H raw2585step0 := by
      have heq : raw2585step0 = raw2585.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2585).symm
    injectiveMoment H raw2585step0 = injectiveMoment H raw2585step1 := by
      have heq : raw2585step1 = (fun i j => raw2585step0 (permutation23 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2585step0 permutation23 permutation20
    _ = injectiveMoment H node1010 := by rfl

def raw2586 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw2586step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![2, -1, -1, 0], ![1, 1, 0, -2]]

def raw2586step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical2586 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2586 = injectiveMoment H node1047 := by
  calc
    injectiveMoment H raw2586 = injectiveMoment H raw2586step0 := by
      have heq : raw2586step0 = raw2586.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2586).symm
    injectiveMoment H raw2586step0 = injectiveMoment H raw2586step1 := by
      have heq : raw2586step1 = (fun i j => raw2586step0 (permutation24 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2586step0 permutation24 permutation24
    _ = injectiveMoment H node1047 := by rfl

def raw2587 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw2587step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 1, 0], ![2, -1, -1, 0], ![1, 1, -1, -1]]

def raw2587step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![-1, -1, 1, 1]]

def raw2587step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical2587 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2587 = injectiveMoment H node1260 := by
  calc
    injectiveMoment H raw2587 = injectiveMoment H raw2587step0 := by
      have heq : raw2587step0 = raw2587.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2587).symm
    injectiveMoment H raw2587step0 = injectiveMoment H raw2587step1 := by
      have heq : raw2587step1 = -raw2587step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2587step0).symm
    injectiveMoment H raw2587step1 = injectiveMoment H raw2587step2 := by
      have heq : raw2587step2 = (fun i j => raw2587step1 (permutation9 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2587step1 permutation9 permutation30
    _ = injectiveMoment H node1260 := by rfl

def raw2588 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw2588step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, 0, 0], ![2, 0, 0, -2, 0], ![1, 0, -1, 1, -1]]

def raw2588step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![1, -1, 1, -1]]

def raw2588step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2588 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2588 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw2588 = injectiveMoment H raw2588step0 := by
      have heq : raw2588step0 = raw2588.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2588).symm
    injectiveMoment H raw2588step0 = injectiveMoment H raw2588step1 := by
      have hz : ∀ i, raw2588step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2588step1 = (fun i j => raw2588step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2588step0 permutation57 hz
    injectiveMoment H raw2588step1 = injectiveMoment H raw2588step2 := by
      have heq : raw2588step2 = (fun i j => raw2588step1 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2588step1 permutation32 permutation30
    _ = injectiveMoment H node1110 := by rfl

def raw2589 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw2589step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![2, -3, 0, 1], ![1, 2, 0, -3]]

def raw2589step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-2, 3, 0, -1], ![-1, -2, 0, 3]]

def raw2589step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 3, -2, -1], ![1, -1, -1, 1]]

theorem canonical2589 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2589 = injectiveMoment H node1018 := by
  calc
    injectiveMoment H raw2589 = injectiveMoment H raw2589step0 := by
      have heq : raw2589step0 = raw2589.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2589).symm
    injectiveMoment H raw2589step0 = injectiveMoment H raw2589step1 := by
      have heq : raw2589step1 = -raw2589step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2589step0).symm
    injectiveMoment H raw2589step1 = injectiveMoment H raw2589step2 := by
      have heq : raw2589step2 = (fun i j => raw2589step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2589step1 permutation12 permutation26
    _ = injectiveMoment H node1018 := by rfl

def raw2590 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -2, 1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2590step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 1, 0, 0, 0], ![2, -2, 0, 0, 0], ![1, 1, 0, -1, -1]]

def raw2590step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, -1, 0, 0, 0], ![-2, 2, 0, 0, 0], ![-1, -1, 0, 1, 1]]

def raw2590step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![-1, -1, 1, 1]]

def raw2590step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical2590 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2590 = injectiveMoment H node1040 := by
  calc
    injectiveMoment H raw2590 = injectiveMoment H raw2590step0 := by
      have heq : raw2590step0 = raw2590.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2590).symm
    injectiveMoment H raw2590step0 = injectiveMoment H raw2590step1 := by
      have heq : raw2590step1 = -raw2590step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2590step0).symm
    injectiveMoment H raw2590step1 = injectiveMoment H raw2590step2 := by
      have hz : ∀ i, raw2590step1 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw2590step2 = (fun i j => raw2590step1 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2590step1 permutation80 hz
    injectiveMoment H raw2590step2 = injectiveMoment H raw2590step3 := by
      have heq : raw2590step3 = (fun i j => raw2590step2 (permutation9 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2590step2 permutation9 permutation26
    _ = injectiveMoment H node1040 := by rfl

def raw2591 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw2591step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![2, -2, -1, 1], ![1, 1, 0, -2]]

def raw2591step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

theorem canonical2591 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2591 = injectiveMoment H node842 := by
  calc
    injectiveMoment H raw2591 = injectiveMoment H raw2591step0 := by
      have heq : raw2591step0 = raw2591.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2591).symm
    injectiveMoment H raw2591step0 = injectiveMoment H raw2591step1 := by
      have heq : raw2591step1 = (fun i j => raw2591step0 (permutation22 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2591step0 permutation22 permutation24
    _ = injectiveMoment H node842 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
