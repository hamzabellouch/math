import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7712 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![-1, 1], ![1, -1]]

def raw7712step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7712step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7712 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7712 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7712 = injectiveMoment H raw7712step0 := by
      have hz : ∀ j, raw7712 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw7712step0 = (fun i j => raw7712 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7712 permutation57 hz
    injectiveMoment H raw7712step0 = injectiveMoment H raw7712step1 := by
      have heq : raw7712step1 = (fun i j => raw7712step0 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7712step0 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw7713 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![0, 0], ![0, 0]]

def raw7713step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![0, 0]]

def raw7713step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1]]

def raw7713step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical7713 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7713 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7713 = injectiveMoment H raw7713step0 := by
      have hz : ∀ j, raw7713 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7713step0 = (fun i j => raw7713 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7713 permutation128 hz
    injectiveMoment H raw7713step0 = injectiveMoment H raw7713step1 := by
      have hz : ∀ j, raw7713step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7713step1 = (fun i j => raw7713step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7713step0 permutation27 hz
    injectiveMoment H raw7713step1 = injectiveMoment H raw7713step2 := by
      have hz : ∀ j, raw7713step1 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw7713step2 = (fun i j => raw7713step1 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7713step1 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

def raw7714 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![-1, 1]]

def raw7714step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7714step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7714 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7714 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7714 = injectiveMoment H raw7714step0 := by
      have hz : ∀ j, raw7714 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw7714step0 = (fun i j => raw7714 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7714 permutation57 hz
    injectiveMoment H raw7714step0 = injectiveMoment H raw7714step1 := by
      have heq : raw7714step1 = (fun i j => raw7714step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7714step0 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw7715 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![0, 0], ![-1, 1]]

def raw7715step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![-1, 1]]

def raw7715step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7715step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7715 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7715 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7715 = injectiveMoment H raw7715step0 := by
      have hz : ∀ j, raw7715 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7715step0 = (fun i j => raw7715 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7715 permutation258 hz
    injectiveMoment H raw7715step0 = injectiveMoment H raw7715step1 := by
      have hz : ∀ j, raw7715step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw7715step1 = (fun i j => raw7715step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7715step0 permutation57 hz
    injectiveMoment H raw7715step1 = injectiveMoment H raw7715step2 := by
      have heq : raw7715step2 = (fun i j => raw7715step1 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7715step1 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw7716 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![2, -2], ![-1, 1]]

def raw7716step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7716step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7716 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7716 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7716 = injectiveMoment H raw7716step0 := by
      have hz : ∀ j, raw7716 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw7716step0 = (fun i j => raw7716 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7716 permutation15 hz
    injectiveMoment H raw7716step0 = injectiveMoment H raw7716step1 := by
      have heq : raw7716step1 = (fun i j => raw7716step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7716step0 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7717 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![2, -2], ![0, 0], ![-1, 1]]

def raw7717step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![2, -2], ![-1, 1]]

def raw7717step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![2, -2], ![-1, 1]]

def raw7717step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7717 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7717 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7717 = injectiveMoment H raw7717step0 := by
      have hz : ∀ j, raw7717 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7717step0 = (fun i j => raw7717 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7717 permutation104 hz
    injectiveMoment H raw7717step0 = injectiveMoment H raw7717step1 := by
      have hz : ∀ j, raw7717step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw7717step1 = (fun i j => raw7717step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7717step0 permutation15 hz
    injectiveMoment H raw7717step1 = injectiveMoment H raw7717step2 := by
      have heq : raw7717step2 = (fun i j => raw7717step1 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7717step1 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7718 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical7718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7718 = injectiveMoment H node5 := by
  rfl

def raw7719 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![0, 0], ![2, -2]]

def raw7719step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw7719step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7719 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7719 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7719 = injectiveMoment H raw7719step0 := by
      have hz : ∀ j, raw7719 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7719step0 = (fun i j => raw7719 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7719 permutation104 hz
    injectiveMoment H raw7719step0 = injectiveMoment H raw7719step1 := by
      have heq : raw7719step1 = (fun i j => raw7719step0 (permutation21 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7719step0 permutation21 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7720 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![1, -1], ![1, -1]]

def raw7720step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7720 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7720 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7720 = injectiveMoment H raw7720step0 := by
      have heq : raw7720step0 = (fun i j => raw7720 (permutation80 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7720 permutation80 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw7721 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![1, -1], ![1, -1], ![0, 0]]

def raw7721step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![1, -1], ![1, -1]]

def raw7721step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7721 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7721 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7721 = injectiveMoment H raw7721step0 := by
      have hz : ∀ j, raw7721 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7721step0 = (fun i j => raw7721 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7721 permutation308 hz
    injectiveMoment H raw7721step0 = injectiveMoment H raw7721step1 := by
      have heq : raw7721step1 = (fun i j => raw7721step0 (permutation80 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7721step0 permutation80 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw7722 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw7722step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7722 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7722 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7722 = injectiveMoment H raw7722step0 := by
      have heq : raw7722step0 = (fun i j => raw7722 (permutation21 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7722 permutation21 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7723 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2], ![0, 0]]

def raw7723step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw7723step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7723 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7723 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7723 = injectiveMoment H raw7723step0 := by
      have hz : ∀ j, raw7723 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7723step0 = (fun i j => raw7723 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7723 permutation128 hz
    injectiveMoment H raw7723step0 = injectiveMoment H raw7723step1 := by
      have heq : raw7723step1 = (fun i j => raw7723step0 (permutation21 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7723step0 permutation21 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7724 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2], ![0, 0], ![0, 0]]

def raw7724step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2], ![0, 0]]

def raw7724step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw7724step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7724 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7724 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7724 = injectiveMoment H raw7724step0 := by
      have hz : ∀ j, raw7724 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7724step0 = (fun i j => raw7724 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7724 permutation308 hz
    injectiveMoment H raw7724step0 = injectiveMoment H raw7724step1 := by
      have hz : ∀ j, raw7724step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7724step1 = (fun i j => raw7724step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7724step0 permutation128 hz
    injectiveMoment H raw7724step1 = injectiveMoment H raw7724step2 := by
      have heq : raw7724step2 = (fun i j => raw7724step1 (permutation21 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7724step1 permutation21 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7725 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7725step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7725 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7725 = injectiveMoment H node383 := by
  calc
    injectiveMoment H raw7725 = injectiveMoment H raw7725step0 := by
      have heq : raw7725step0 = (fun i j => raw7725 (permutation331 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7725 permutation331 permutation2
    _ = injectiveMoment H node383 := by rfl

def raw7726 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw7726step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2]]

def raw7726step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7726 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7726 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7726 = injectiveMoment H raw7726step0 := by
      have hz : ∀ j, raw7726 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7726step0 = (fun i j => raw7726 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7726 permutation258 hz
    injectiveMoment H raw7726step0 = injectiveMoment H raw7726step1 := by
      have heq : raw7726step1 = (fun i j => raw7726step0 (permutation133 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7726step0 permutation133 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7727 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw7727step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7727 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7727 = injectiveMoment H node1323 := by
  calc
    injectiveMoment H raw7727 = injectiveMoment H raw7727step0 := by
      have heq : raw7727step0 = (fun i j => raw7727 (permutation169 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7727 permutation169 permutation1
    _ = injectiveMoment H node1323 := by rfl

def raw7728 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2]]

def raw7728step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7728 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7728 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7728 = injectiveMoment H raw7728step0 := by
      have heq : raw7728step0 = (fun i j => raw7728 (permutation133 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7728 permutation133 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7729 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![0, 0], ![0, 0], ![1, -1]]

def raw7729step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![0, 0], ![1, -1]]

def raw7729step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7729step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7729 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7729 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7729 = injectiveMoment H raw7729step0 := by
      have hz : ∀ j, raw7729 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7729step0 = (fun i j => raw7729 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7729 permutation258 hz
    injectiveMoment H raw7729step0 = injectiveMoment H raw7729step1 := by
      have hz : ∀ j, raw7729step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7729step1 = (fun i j => raw7729step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7729step0 permutation104 hz
    injectiveMoment H raw7729step1 = injectiveMoment H raw7729step2 := by
      have heq : raw7729step2 = (fun i j => raw7729step1 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7729step1 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw7730 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![0, 0], ![1, -1]]

def raw7730step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7730step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7730 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7730 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7730 = injectiveMoment H raw7730step0 := by
      have hz : ∀ j, raw7730 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7730step0 = (fun i j => raw7730 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7730 permutation104 hz
    injectiveMoment H raw7730step0 = injectiveMoment H raw7730step1 := by
      have heq : raw7730step1 = (fun i j => raw7730step0 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7730step0 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw7731 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7731step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7731 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7731 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7731 = injectiveMoment H raw7731step0 := by
      have heq : raw7731step0 = (fun i j => raw7731 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7731 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw7732 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![0, 0]]

def raw7732step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7732step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7732 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7732 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7732 = injectiveMoment H raw7732step0 := by
      have hz : ∀ j, raw7732 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7732step0 = (fun i j => raw7732 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7732 permutation128 hz
    injectiveMoment H raw7732step0 = injectiveMoment H raw7732step1 := by
      have heq : raw7732step1 = (fun i j => raw7732step0 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7732step0 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw7733 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![0, 0], ![0, 0]]

def raw7733step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![0, 0]]

def raw7733step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7733step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7733 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7733 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7733 = injectiveMoment H raw7733step0 := by
      have hz : ∀ j, raw7733 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7733step0 = (fun i j => raw7733 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7733 permutation308 hz
    injectiveMoment H raw7733step0 = injectiveMoment H raw7733step1 := by
      have hz : ∀ j, raw7733step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7733step1 = (fun i j => raw7733step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7733step0 permutation128 hz
    injectiveMoment H raw7733step1 = injectiveMoment H raw7733step2 := by
      have heq : raw7733step2 = (fun i j => raw7733step1 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7733step1 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw7734 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7734step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7734 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7734 = injectiveMoment H node1323 := by
  calc
    injectiveMoment H raw7734 = injectiveMoment H raw7734step0 := by
      have heq : raw7734step0 = (fun i j => raw7734 (permutation175 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7734 permutation175 permutation1
    _ = injectiveMoment H node1323 := by rfl

def raw7735 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0]]

def raw7735step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical7735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7735 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7735 = injectiveMoment H raw7735step0 := by
      have hz : ∀ j, raw7735 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7735step0 = (fun i j => raw7735 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7735 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

def raw7736 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![0, 0]]

def raw7736step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0]]

def raw7736step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical7736 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7736 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7736 = injectiveMoment H raw7736step0 := by
      have hz : ∀ j, raw7736 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7736step0 = (fun i j => raw7736 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7736 permutation27 hz
    injectiveMoment H raw7736step0 = injectiveMoment H raw7736step1 := by
      have hz : ∀ j, raw7736step0 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7736step1 = (fun i j => raw7736step0 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7736step0 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

def raw7737 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![0, 0], ![0, 0]]

def raw7737step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![0, 0]]

def raw7737step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0]]

def raw7737step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical7737 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7737 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7737 = injectiveMoment H raw7737step0 := by
      have hz : ∀ j, raw7737 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7737step0 = (fun i j => raw7737 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7737 permutation128 hz
    injectiveMoment H raw7737step0 = injectiveMoment H raw7737step1 := by
      have hz : ∀ j, raw7737step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7737step1 = (fun i j => raw7737step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7737step0 permutation27 hz
    injectiveMoment H raw7737step1 = injectiveMoment H raw7737step2 := by
      have hz : ∀ j, raw7737step1 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7737step2 = (fun i j => raw7737step1 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7737step1 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

def raw7738 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7738step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7738 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7738 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7738 = injectiveMoment H raw7738step0 := by
      have heq : raw7738step0 = (fun i j => raw7738 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7738 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw7739 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1], ![-1, 1], ![1, -1]]

def raw7739step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7739 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7739 = injectiveMoment H node1323 := by
  calc
    injectiveMoment H raw7739 = injectiveMoment H raw7739step0 := by
      have heq : raw7739step0 = (fun i j => raw7739 (permutation178 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7739 permutation178 permutation1
    _ = injectiveMoment H node1323 := by rfl

def raw7740 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1], ![0, 0]]

def raw7740step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7740step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7740 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7740 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7740 = injectiveMoment H raw7740step0 := by
      have hz : ∀ j, raw7740 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7740step0 = (fun i j => raw7740 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7740 permutation128 hz
    injectiveMoment H raw7740step0 = injectiveMoment H raw7740step1 := by
      have heq : raw7740step1 = (fun i j => raw7740step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7740step0 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw7741 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1], ![0, 0], ![0, 0]]

def raw7741step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1], ![0, 0]]

def raw7741step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7741step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7741 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7741 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7741 = injectiveMoment H raw7741step0 := by
      have hz : ∀ j, raw7741 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7741step0 = (fun i j => raw7741 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7741 permutation308 hz
    injectiveMoment H raw7741step0 = injectiveMoment H raw7741step1 := by
      have hz : ∀ j, raw7741step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7741step1 = (fun i j => raw7741step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7741step0 permutation128 hz
    injectiveMoment H raw7741step1 = injectiveMoment H raw7741step2 := by
      have heq : raw7741step2 = (fun i j => raw7741step1 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7741step1 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw7742 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![-1, 1]]

def raw7742step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7742step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7742 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7742 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7742 = injectiveMoment H raw7742step0 := by
      have hz : ∀ j, raw7742 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7742step0 = (fun i j => raw7742 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7742 permutation104 hz
    injectiveMoment H raw7742step0 = injectiveMoment H raw7742step1 := by
      have heq : raw7742step1 = (fun i j => raw7742step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7742step0 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw7743 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![0, 0], ![-1, 1]]

def raw7743step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![-1, 1]]

def raw7743step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7743step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7743 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7743 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7743 = injectiveMoment H raw7743step0 := by
      have hz : ∀ j, raw7743 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7743step0 = (fun i j => raw7743 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7743 permutation258 hz
    injectiveMoment H raw7743step0 = injectiveMoment H raw7743step1 := by
      have hz : ∀ j, raw7743step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7743step1 = (fun i j => raw7743step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7743step0 permutation104 hz
    injectiveMoment H raw7743step1 = injectiveMoment H raw7743step2 := by
      have heq : raw7743step2 = (fun i j => raw7743step1 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7743step1 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
