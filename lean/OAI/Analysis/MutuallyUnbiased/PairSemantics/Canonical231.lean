import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7392 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7392 = injectiveMoment H node2796 := by
  rfl

def raw7393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]

def raw7393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, -1, 3]]

def raw7393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7393 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7393 = injectiveMoment H node1885 := by
  calc
    injectiveMoment H raw7393 = injectiveMoment H raw7393step0 := by
      have heq : raw7393step0 = -raw7393 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7393).symm
    injectiveMoment H raw7393step0 = injectiveMoment H raw7393step1 := by
      have heq : raw7393step1 = (fun i j => raw7393step0 (permutation367 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7393step0 permutation367 permutation3
    _ = injectiveMoment H node1885 := by rfl

def raw7394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3], ![2, 1, -3]]

def raw7394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical7394 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7394 = injectiveMoment H node1861 := by
  calc
    injectiveMoment H raw7394 = injectiveMoment H raw7394step0 := by
      have heq : raw7394step0 = (fun i j => raw7394 (permutation288 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7394 permutation288 permutation5
    _ = injectiveMoment H node1861 := by rfl

def raw7395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2]]

def raw7395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, -1, 2]]

def raw7395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7395 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7395 = injectiveMoment H node2666 := by
  calc
    injectiveMoment H raw7395 = injectiveMoment H raw7395step0 := by
      have heq : raw7395step0 = -raw7395 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7395).symm
    injectiveMoment H raw7395step0 = injectiveMoment H raw7395step1 := by
      have heq : raw7395step1 = (fun i j => raw7395step0 (permutation388 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7395step0 permutation388 permutation3
    _ = injectiveMoment H node2666 := by rfl

def raw7396 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw7396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical7396 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7396 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H raw7396 = injectiveMoment H raw7396step0 := by
      have heq : raw7396step0 = (fun i j => raw7396 (permutation89 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7396 permutation89 permutation7
    _ = injectiveMoment H node1294 := by rfl

def raw7397 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw7397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1]]

def raw7397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7397 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7397 = injectiveMoment H node869 := by
  calc
    injectiveMoment H raw7397 = injectiveMoment H raw7397step0 := by
      have heq : raw7397step0 = -raw7397 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7397).symm
    injectiveMoment H raw7397step0 = injectiveMoment H raw7397step1 := by
      have heq : raw7397step1 = (fun i j => raw7397step0 (permutation126 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7397step0 permutation126 permutation4
    _ = injectiveMoment H node869 := by rfl

def raw7398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![-1, 3, -2], ![1, -3, 2]]

def raw7398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

theorem canonical7398 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7398 = injectiveMoment H node1858 := by
  calc
    injectiveMoment H raw7398 = injectiveMoment H raw7398step0 := by
      have heq : raw7398step0 = (fun i j => raw7398 (permutation290 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7398 permutation290 permutation7
    _ = injectiveMoment H node1858 := by rfl

def raw7399 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

def raw7399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical7399 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7399 = injectiveMoment H node655 := by
  calc
    injectiveMoment H raw7399 = injectiveMoment H raw7399step0 := by
      have heq : raw7399step0 = (fun i j => raw7399 (permutation83 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7399 permutation83 permutation5
    _ = injectiveMoment H node655 := by rfl

def raw7400 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]

def raw7400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, -3, 2], ![0, 3, -3], ![-1, 0, 1], ![-1, 0, 1]]

def raw7400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical7400 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7400 = injectiveMoment H node1287 := by
  calc
    injectiveMoment H raw7400 = injectiveMoment H raw7400step0 := by
      have heq : raw7400step0 = -raw7400 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7400).symm
    injectiveMoment H raw7400step0 = injectiveMoment H raw7400step1 := by
      have heq : raw7400step1 = (fun i j => raw7400step0 (permutation127 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7400step0 permutation127 permutation3
    _ = injectiveMoment H node1287 := by rfl

def raw7401 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![1, -3, 2], ![1, 0, -1]]

def raw7401step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical7401 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7401 = injectiveMoment H node259 := by
  calc
    injectiveMoment H raw7401 = injectiveMoment H raw7401step0 := by
      have heq : raw7401step0 = (fun i j => raw7401 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7401 permutation16 permutation4
    _ = injectiveMoment H node259 := by rfl

def raw7402 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 4, -3], ![1, -2, 1], ![1, -2, 1]]

def raw7402step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

theorem canonical7402 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7402 = injectiveMoment H node244 := by
  calc
    injectiveMoment H raw7402 = injectiveMoment H raw7402step0 := by
      have heq : raw7402step0 = (fun i j => raw7402 (permutation15 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7402 permutation15 permutation4
    _ = injectiveMoment H node244 := by rfl

def raw7403 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def raw7403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1]]

def raw7403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical7403 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7403 = injectiveMoment H node1287 := by
  calc
    injectiveMoment H raw7403 = injectiveMoment H raw7403step0 := by
      have heq : raw7403step0 = -raw7403 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7403).symm
    injectiveMoment H raw7403step0 = injectiveMoment H raw7403step1 := by
      have heq : raw7403step1 = (fun i j => raw7403step0 (permutation125 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7403step0 permutation125 permutation3
    _ = injectiveMoment H node1287 := by rfl

def raw7404 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 2, -2], ![1, 1, -2]]

def raw7404step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![0, -2, 2], ![-1, -1, 2]]

def raw7404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7404 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7404 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw7404 = injectiveMoment H raw7404step0 := by
      have heq : raw7404step0 = -raw7404 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7404).symm
    injectiveMoment H raw7404step0 = injectiveMoment H raw7404step1 := by
      have heq : raw7404step1 = (fun i j => raw7404step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7404step0 permutation32 permutation3
    _ = injectiveMoment H node280 := by rfl

def raw7405 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1]]

def raw7405step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7405 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7405 = injectiveMoment H node289 := by
  calc
    injectiveMoment H raw7405 = injectiveMoment H raw7405step0 := by
      have hz : ∀ j, raw7405 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7405step0 = (fun i j => raw7405 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7405 permutation104 hz
    _ = injectiveMoment H node289 := by rfl

def raw7406 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7406 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7406 = injectiveMoment H node289 := by
  rfl

def raw7407 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1], ![0, 0, 0]]

def raw7407step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7407 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7407 = injectiveMoment H node289 := by
  calc
    injectiveMoment H raw7407 = injectiveMoment H raw7407step0 := by
      have hz : ∀ j, raw7407 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7407step0 = (fun i j => raw7407 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7407 permutation128 hz
    _ = injectiveMoment H node289 := by rfl

def raw7408 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![1, 3, -4]]

def raw7408step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-1, -3, 4]]

def raw7408step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7408 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7408 = injectiveMoment H node53 := by
  calc
    injectiveMoment H raw7408 = injectiveMoment H raw7408step0 := by
      have heq : raw7408step0 = -raw7408 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7408).symm
    injectiveMoment H raw7408step0 = injectiveMoment H raw7408step1 := by
      have heq : raw7408step1 = (fun i j => raw7408step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7408step0 permutation8 permutation3
    _ = injectiveMoment H node53 := by rfl

def raw7409 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw7409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7409 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7409 = injectiveMoment H node869 := by
  calc
    injectiveMoment H raw7409 = injectiveMoment H raw7409step0 := by
      have heq : raw7409step0 = (fun i j => raw7409 (permutation81 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7409 permutation81 permutation4
    _ = injectiveMoment H node869 := by rfl

def raw7410 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![-1, 4, -3], ![1, -1, 0], ![1, -1, 0]]

def raw7410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical7410 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7410 = injectiveMoment H node739 := by
  calc
    injectiveMoment H raw7410 = injectiveMoment H raw7410step0 := by
      have heq : raw7410step0 = (fun i j => raw7410 (permutation80 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7410 permutation80 permutation4
    _ = injectiveMoment H node739 := by rfl

def raw7411 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2]]

def raw7411step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2]]

def raw7411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7411 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7411 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw7411 = injectiveMoment H raw7411step0 := by
      have heq : raw7411step0 = -raw7411 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7411).symm
    injectiveMoment H raw7411step0 = injectiveMoment H raw7411step1 := by
      have heq : raw7411step1 = (fun i j => raw7411step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7411step0 permutation32 permutation3
    _ = injectiveMoment H node284 := by rfl

def raw7412 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7412 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7412 = injectiveMoment H node291 := by
  rfl

def raw7413 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1]]

def raw7413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![0, -3, 3], ![0, 1, -1], ![-1, 0, 1]]

def raw7413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7413 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7413 = injectiveMoment H node1288 := by
  calc
    injectiveMoment H raw7413 = injectiveMoment H raw7413step0 := by
      have heq : raw7413step0 = -raw7413 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7413).symm
    injectiveMoment H raw7413step0 = injectiveMoment H raw7413step1 := by
      have heq : raw7413step1 = (fun i j => raw7413step0 (permutation144 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7413step0 permutation144 permutation3
    _ = injectiveMoment H node1288 := by rfl

def raw7414 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7414 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7414 = injectiveMoment H node292 := by
  rfl

def raw7415 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![0, 0, 0]]

def raw7415step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

theorem canonical7415 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7415 = injectiveMoment H node292 := by
  calc
    injectiveMoment H raw7415 = injectiveMoment H raw7415step0 := by
      have hz : ∀ j, raw7415 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7415step0 = (fun i j => raw7415 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7415 permutation128 hz
    _ = injectiveMoment H node292 := by rfl

def raw7416 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 4, -4], ![0, -1, 1], ![1, -1, 0]]

def raw7416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

theorem canonical7416 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7416 = injectiveMoment H node1290 := by
  calc
    injectiveMoment H raw7416 = injectiveMoment H raw7416step0 := by
      have heq : raw7416step0 = (fun i j => raw7416 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7416 permutation35 permutation3
    _ = injectiveMoment H node1290 := by rfl

def raw7417 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 4, -4], ![1, -2, 1]]

def raw7417step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![0, -4, 4], ![-1, 2, -1]]

def raw7417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

theorem canonical7417 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7417 = injectiveMoment H node281 := by
  calc
    injectiveMoment H raw7417 = injectiveMoment H raw7417step0 := by
      have heq : raw7417step0 = -raw7417 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7417).symm
    injectiveMoment H raw7417step0 = injectiveMoment H raw7417step1 := by
      have heq : raw7417step1 = (fun i j => raw7417step0 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7417step0 permutation30 permutation4
    _ = injectiveMoment H node281 := by rfl

def raw7418 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0], ![0, -1, 1]]

def raw7418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

theorem canonical7418 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7418 = injectiveMoment H node1290 := by
  calc
    injectiveMoment H raw7418 = injectiveMoment H raw7418step0 := by
      have heq : raw7418step0 = (fun i j => raw7418 (permutation37 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7418 permutation37 permutation3
    _ = injectiveMoment H node1290 := by rfl

def raw7419 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![1, 2, -3]]

def raw7419step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-1, -2, 3]]

def raw7419step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7419 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7419 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw7419 = injectiveMoment H raw7419step0 := by
      have heq : raw7419step0 = -raw7419 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7419).symm
    injectiveMoment H raw7419step0 = injectiveMoment H raw7419step1 := by
      have heq : raw7419step1 = (fun i j => raw7419step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7419step0 permutation8 permutation3
    _ = injectiveMoment H node57 := by rfl

def raw7420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def raw7420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, -4, 5]]

def raw7420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical7420 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7420 = injectiveMoment H node2375 := by
  calc
    injectiveMoment H raw7420 = injectiveMoment H raw7420step0 := by
      have heq : raw7420step0 = -raw7420 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7420).symm
    injectiveMoment H raw7420step0 = injectiveMoment H raw7420step1 := by
      have heq : raw7420step1 = (fun i j => raw7420step0 (permutation402 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7420step0 permutation402 permutation3
    _ = injectiveMoment H node2375 := by rfl

def raw7421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def raw7421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -2, 3]]

def raw7421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical7421 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7421 = injectiveMoment H node2466 := by
  calc
    injectiveMoment H raw7421 = injectiveMoment H raw7421step0 := by
      have heq : raw7421step0 = -raw7421 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7421).symm
    injectiveMoment H raw7421step0 = injectiveMoment H raw7421step1 := by
      have heq : raw7421step1 = (fun i j => raw7421step0 (permutation407 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7421step0 permutation407 permutation3
    _ = injectiveMoment H node2466 := by rfl

def raw7422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 4, -4]]

def raw7422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem canonical7422 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7422 = injectiveMoment H node2658 := by
  calc
    injectiveMoment H raw7422 = injectiveMoment H raw7422step0 := by
      have heq : raw7422step0 = (fun i j => raw7422 (permutation224 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7422 permutation224 permutation3
    _ = injectiveMoment H node2658 := by rfl

def raw7423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 3, -3]]

def raw7423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7423 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7423 = injectiveMoment H node2657 := by
  calc
    injectiveMoment H raw7423 = injectiveMoment H raw7423step0 := by
      have heq : raw7423step0 = (fun i j => raw7423 (permutation224 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7423 permutation224 permutation3
    _ = injectiveMoment H node2657 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
