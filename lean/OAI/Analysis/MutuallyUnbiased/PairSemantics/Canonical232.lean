import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw7424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7424 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7424 = injectiveMoment H node2796 := by
  calc
    injectiveMoment H raw7424 = injectiveMoment H raw7424step0 := by
      have heq : raw7424step0 = (fun i j => raw7424 (permutation166 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7424 permutation166 permutation3
    _ = injectiveMoment H node2796 := by rfl

def raw7425 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1]]

def raw7425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7425 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7425 = injectiveMoment H node868 := by
  calc
    injectiveMoment H raw7425 = injectiveMoment H raw7425step0 := by
      have heq : raw7425step0 = (fun i j => raw7425 (permutation81 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7425 permutation81 permutation4
    _ = injectiveMoment H node868 := by rfl

def raw7426 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0]]

def raw7426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7426 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7426 = injectiveMoment H node570 := by
  calc
    injectiveMoment H raw7426 = injectiveMoment H raw7426step0 := by
      have heq : raw7426step0 = (fun i j => raw7426 (permutation96 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7426 permutation96 permutation7
    _ = injectiveMoment H node570 := by rfl

def raw7427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 4, -5]]

def raw7427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, -4, 5]]

def raw7427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical7427 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7427 = injectiveMoment H node2375 := by
  calc
    injectiveMoment H raw7427 = injectiveMoment H raw7427step0 := by
      have heq : raw7427step0 = -raw7427 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7427).symm
    injectiveMoment H raw7427step0 = injectiveMoment H raw7427step1 := by
      have heq : raw7427step1 = (fun i j => raw7427step0 (permutation400 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7427step0 permutation400 permutation3
    _ = injectiveMoment H node2375 := by rfl

def raw7428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw7428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]

def raw7428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7428 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7428 = injectiveMoment H node2469 := by
  calc
    injectiveMoment H raw7428 = injectiveMoment H raw7428step0 := by
      have heq : raw7428step0 = -raw7428 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7428).symm
    injectiveMoment H raw7428step0 = injectiveMoment H raw7428step1 := by
      have heq : raw7428step1 = (fun i j => raw7428step0 (permutation401 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7428step0 permutation401 permutation3
    _ = injectiveMoment H node2469 := by rfl

def raw7429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 4, -5]]

def raw7429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -4, 5]]

def raw7429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical7429 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7429 = injectiveMoment H node2376 := by
  calc
    injectiveMoment H raw7429 = injectiveMoment H raw7429step0 := by
      have heq : raw7429step0 = -raw7429 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7429).symm
    injectiveMoment H raw7429step0 = injectiveMoment H raw7429step1 := by
      have heq : raw7429step1 = (fun i j => raw7429step0 (permutation340 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7429step0 permutation340 permutation3
    _ = injectiveMoment H node2376 := by rfl

def raw7430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 4, -4]]

def raw7430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

theorem canonical7430 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7430 = injectiveMoment H node2799 := by
  calc
    injectiveMoment H raw7430 = injectiveMoment H raw7430step0 := by
      have heq : raw7430step0 = (fun i j => raw7430 (permutation152 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7430 permutation152 permutation3
    _ = injectiveMoment H node2799 := by rfl

def raw7431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 3, -3]]

def raw7431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![0, -3, 3]]

def raw7431step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical7431 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7431 = injectiveMoment H node2797 := by
  calc
    injectiveMoment H raw7431 = injectiveMoment H raw7431step0 := by
      have heq : raw7431step0 = -raw7431 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7431).symm
    injectiveMoment H raw7431step0 = injectiveMoment H raw7431step1 := by
      have heq : raw7431step1 = (fun i j => raw7431step0 (permutation300 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7431step0 permutation300 permutation3
    _ = injectiveMoment H node2797 := by rfl

def raw7432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3]]

def raw7432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![-1, -2, 3]]

def raw7432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical7432 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7432 = injectiveMoment H node2478 := by
  calc
    injectiveMoment H raw7432 = injectiveMoment H raw7432step0 := by
      have heq : raw7432step0 = -raw7432 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7432).symm
    injectiveMoment H raw7432step0 = injectiveMoment H raw7432step1 := by
      have heq : raw7432step1 = (fun i j => raw7432step0 (permutation380 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7432step0 permutation380 permutation3
    _ = injectiveMoment H node2478 := by rfl

def raw7433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 2, -2]]

def raw7433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical7433 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7433 = injectiveMoment H node2801 := by
  calc
    injectiveMoment H raw7433 = injectiveMoment H raw7433step0 := by
      have heq : raw7433step0 = (fun i j => raw7433 (permutation152 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7433 permutation152 permutation3
    _ = injectiveMoment H node2801 := by rfl

def raw7434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, -1, 1], ![0, 4, -4]]

def raw7434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

theorem canonical7434 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7434 = injectiveMoment H node2799 := by
  calc
    injectiveMoment H raw7434 = injectiveMoment H raw7434step0 := by
      have heq : raw7434step0 = (fun i j => raw7434 (permutation154 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7434 permutation154 permutation3
    _ = injectiveMoment H node2799 := by rfl

def raw7435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3]]

def raw7435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 3, -3]]

def raw7435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7435 = injectiveMoment H node1293 := by
  calc
    injectiveMoment H raw7435 = injectiveMoment H raw7435step0 := by
      have hz : ∀ j, raw7435 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7435step0 = (fun i j => raw7435 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7435 permutation258 hz
    injectiveMoment H raw7435step0 = injectiveMoment H raw7435step1 := by
      have heq : raw7435step1 = (fun i j => raw7435step0 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7435step0 permutation34 permutation3
    _ = injectiveMoment H node1293 := by rfl

def raw7436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-1, 4, -3]]

def raw7436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical7436 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7436 = injectiveMoment H node2380 := by
  calc
    injectiveMoment H raw7436 = injectiveMoment H raw7436step0 := by
      have heq : raw7436step0 = (fun i j => raw7436 (permutation308 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7436 permutation308 permutation4
    _ = injectiveMoment H node2380 := by rfl

def raw7437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 3, -2]]

def raw7437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7437 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7437 = injectiveMoment H node2469 := by
  calc
    injectiveMoment H raw7437 = injectiveMoment H raw7437step0 := by
      have heq : raw7437step0 = (fun i j => raw7437 (permutation309 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7437 permutation309 permutation4
    _ = injectiveMoment H node2469 := by rfl

def raw7438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw7438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7438 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7438 = injectiveMoment H node2796 := by
  calc
    injectiveMoment H raw7438 = injectiveMoment H raw7438step0 := by
      have heq : raw7438step0 = (fun i j => raw7438 (permutation176 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7438 permutation176 permutation3
    _ = injectiveMoment H node2796 := by rfl

def raw7439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1]]

def raw7439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical7439 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7439 = injectiveMoment H node2800 := by
  calc
    injectiveMoment H raw7439 = injectiveMoment H raw7439step0 := by
      have heq : raw7439step0 = (fun i j => raw7439 (permutation162 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7439 permutation162 permutation3
    _ = injectiveMoment H node2800 := by rfl

def raw7440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]

def raw7440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical7440 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7440 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H raw7440 = injectiveMoment H raw7440step0 := by
      have hz : ∀ j, raw7440 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7440step0 = (fun i j => raw7440 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7440 permutation308 hz
    _ = injectiveMoment H node1294 := by rfl

def raw7441 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1]]

def raw7441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, -3, 3], ![0, 2, -2], ![-1, 0, 1]]

def raw7441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7441 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7441 = injectiveMoment H node1288 := by
  calc
    injectiveMoment H raw7441 = injectiveMoment H raw7441step0 := by
      have heq : raw7441step0 = -raw7441 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7441).symm
    injectiveMoment H raw7441step0 = injectiveMoment H raw7441step1 := by
      have heq : raw7441step1 = (fun i j => raw7441step0 (permutation142 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7441step0 permutation142 permutation3
    _ = injectiveMoment H node1288 := by rfl

def raw7442 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0]]

def raw7442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7442 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7442 = injectiveMoment H node1293 := by
  calc
    injectiveMoment H raw7442 = injectiveMoment H raw7442step0 := by
      have heq : raw7442step0 = (fun i j => raw7442 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7442 permutation35 permutation3
    _ = injectiveMoment H node1293 := by rfl

def raw7443 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![0, 0, 0]]

def raw7443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, -3, 3], ![-1, 2, -1], ![0, 0, 0]]

def raw7443step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![0, -3, 3], ![-1, 2, -1]]

def raw7443step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7443 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7443 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw7443 = injectiveMoment H raw7443step0 := by
      have heq : raw7443step0 = -raw7443 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7443).symm
    injectiveMoment H raw7443step0 = injectiveMoment H raw7443step1 := by
      have hz : ∀ j, raw7443step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7443step1 = (fun i j => raw7443step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7443step0 permutation128 hz
    injectiveMoment H raw7443step1 = injectiveMoment H raw7443step2 := by
      have heq : raw7443step2 = (fun i j => raw7443step1 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7443step1 permutation30 permutation4
    _ = injectiveMoment H node285 := by rfl

def raw7444 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![0, -1, 1]]

def raw7444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7444 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7444 = injectiveMoment H node1293 := by
  calc
    injectiveMoment H raw7444 = injectiveMoment H raw7444step0 := by
      have heq : raw7444step0 = (fun i j => raw7444 (permutation37 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7444 permutation37 permutation3
    _ = injectiveMoment H node1293 := by rfl

def raw7445 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]

def raw7445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical7445 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7445 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H raw7445 = injectiveMoment H raw7445step0 := by
      have heq : raw7445step0 = (fun i j => raw7445 (permutation65 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7445 permutation65 permutation7
    _ = injectiveMoment H node1294 := by rfl

def raw7446 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1]]

def raw7446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![-1, 3, -2], ![-1, 0, 1]]

def raw7446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7446 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7446 = injectiveMoment H node868 := by
  calc
    injectiveMoment H raw7446 = injectiveMoment H raw7446step0 := by
      have heq : raw7446step0 = -raw7446 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7446).symm
    injectiveMoment H raw7446step0 = injectiveMoment H raw7446step1 := by
      have heq : raw7446step1 = (fun i j => raw7446step0 (permutation124 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7446step0 permutation124 permutation4
    _ = injectiveMoment H node868 := by rfl

def raw7447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![-1, 3, -2], ![1, -3, 2]]

def raw7447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical7447 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7447 = injectiveMoment H node2465 := by
  calc
    injectiveMoment H raw7447 = injectiveMoment H raw7447step0 := by
      have heq : raw7447step0 = (fun i j => raw7447 (permutation258 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7447 permutation258 permutation4
    _ = injectiveMoment H node2465 := by rfl

def raw7448 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0]]

def raw7448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical7448 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7448 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H raw7448 = injectiveMoment H raw7448step0 := by
      have heq : raw7448step0 = (fun i j => raw7448 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7448 permutation45 permutation3
    _ = injectiveMoment H node1294 := by rfl

def raw7449 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

def raw7449step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1]]

def raw7449step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical7449 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7449 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw7449 = injectiveMoment H raw7449step0 := by
      have heq : raw7449step0 = -raw7449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7449).symm
    injectiveMoment H raw7449step0 = injectiveMoment H raw7449step1 := by
      have heq : raw7449step1 = (fun i j => raw7449step0 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7449step0 permutation30 permutation4
    _ = injectiveMoment H node287 := by rfl

def raw7450 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1]]

def raw7450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical7450 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7450 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H raw7450 = injectiveMoment H raw7450step0 := by
      have heq : raw7450step0 = (fun i j => raw7450 (permutation51 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7450 permutation51 permutation3
    _ = injectiveMoment H node1294 := by rfl

def raw7451 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![0, -3, 3], ![1, 0, -1]]

def raw7451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7451 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7451 = injectiveMoment H node1288 := by
  calc
    injectiveMoment H raw7451 = injectiveMoment H raw7451step0 := by
      have heq : raw7451step0 = (fun i j => raw7451 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7451 permutation45 permutation3
    _ = injectiveMoment H node1288 := by rfl

def raw7452 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![0, 0, 0]]

def raw7452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![0, 0, 0]]

def raw7452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2]]

def raw7452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical7452 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7452 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw7452 = injectiveMoment H raw7452step0 := by
      have heq : raw7452step0 = -raw7452 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7452).symm
    injectiveMoment H raw7452step0 = injectiveMoment H raw7452step1 := by
      have hz : ∀ j, raw7452step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7452step1 = (fun i j => raw7452step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7452step0 permutation128 hz
    injectiveMoment H raw7452step1 = injectiveMoment H raw7452step2 := by
      have heq : raw7452step2 = (fun i j => raw7452step1 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7452step1 permutation30 permutation4
    _ = injectiveMoment H node272 := by rfl

def raw7453 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical7453 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7453 = injectiveMoment H node64 := by
  rfl

def raw7454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -3, 2]]

def raw7454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, 3, -2]]

def raw7454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![1, -3, 2], ![-1, 3, -2]]

def raw7454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical7454 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7454 = injectiveMoment H node862 := by
  calc
    injectiveMoment H raw7454 = injectiveMoment H raw7454step0 := by
      have heq : raw7454step0 = -raw7454 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7454).symm
    injectiveMoment H raw7454step0 = injectiveMoment H raw7454step1 := by
      have hz : ∀ j, raw7454step0 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw7454step1 = (fun i j => raw7454step0 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7454step0 permutation241 hz
    injectiveMoment H raw7454step1 = injectiveMoment H raw7454step2 := by
      have heq : raw7454step2 = (fun i j => raw7454step1 (permutation141 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7454step1 permutation141 permutation4
    _ = injectiveMoment H node862 := by rfl

def raw7455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def raw7455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical7455 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7455 = injectiveMoment H node1861 := by
  calc
    injectiveMoment H raw7455 = injectiveMoment H raw7455step0 := by
      have heq : raw7455step0 = (fun i j => raw7455 (permutation260 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7455 permutation260 permutation4
    _ = injectiveMoment H node1861 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
