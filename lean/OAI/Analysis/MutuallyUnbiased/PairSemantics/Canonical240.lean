import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7680 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![0, 0]]

def raw7680step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![0, 0]]

def raw7680step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7680 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7680 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7680 = injectiveMoment H raw7680step0 := by
      have hz : ∀ j, raw7680 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7680step0 = (fun i j => raw7680 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7680 permutation308 hz
    injectiveMoment H raw7680step0 = injectiveMoment H raw7680step1 := by
      have hz : ∀ j, raw7680step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7680step1 = (fun i j => raw7680step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7680step0 permutation128 hz
    _ = injectiveMoment H node65 := by rfl

def raw7681 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]

def raw7681step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7681 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7681 = injectiveMoment H node1323 := by
  calc
    injectiveMoment H raw7681 = injectiveMoment H raw7681step0 := by
      have heq : raw7681step0 = (fun i j => raw7681 (permutation165 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7681 permutation165 permutation1
    _ = injectiveMoment H node1323 := by rfl

def raw7682 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![-1, 1]]

def raw7682step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7682 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7682 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7682 = injectiveMoment H raw7682step0 := by
      have heq : raw7682step0 = (fun i j => raw7682 (permutation116 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7682 permutation116 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7683 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7683step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7683 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7683 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7683 = injectiveMoment H raw7683step0 := by
      have heq : raw7683step0 = (fun i j => raw7683 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7683 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7684 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![-1, 1], ![1, -1]]

def raw7684step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7684 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7684 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7684 = injectiveMoment H raw7684step0 := by
      have heq : raw7684step0 = (fun i j => raw7684 (permutation98 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7684 permutation98 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7685 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![0, 0]]

def raw7685step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7685step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7685 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7685 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7685 = injectiveMoment H raw7685step0 := by
      have hz : ∀ j, raw7685 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7685step0 = (fun i j => raw7685 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7685 permutation27 hz
    injectiveMoment H raw7685step0 = injectiveMoment H raw7685step1 := by
      have heq : raw7685step1 = (fun i j => raw7685step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7685step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7686 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![0, 0], ![0, 0]]

def raw7686step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![0, 0]]

def raw7686step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7686step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7686 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7686 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7686 = injectiveMoment H raw7686step0 := by
      have hz : ∀ j, raw7686 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7686step0 = (fun i j => raw7686 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7686 permutation128 hz
    injectiveMoment H raw7686step0 = injectiveMoment H raw7686step1 := by
      have hz : ∀ j, raw7686step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7686step1 = (fun i j => raw7686step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7686step0 permutation27 hz
    injectiveMoment H raw7686step1 = injectiveMoment H raw7686step2 := by
      have heq : raw7686step2 = (fun i j => raw7686step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7686step1 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7687 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![0, 0], ![0, 0], ![0, 0]]

def raw7687step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![0, 0], ![0, 0]]

def raw7687step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![0, 0]]

def raw7687step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7687step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7687 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7687 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7687 = injectiveMoment H raw7687step0 := by
      have hz : ∀ j, raw7687 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7687step0 = (fun i j => raw7687 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7687 permutation308 hz
    injectiveMoment H raw7687step0 = injectiveMoment H raw7687step1 := by
      have hz : ∀ j, raw7687step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7687step1 = (fun i j => raw7687step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7687step0 permutation128 hz
    injectiveMoment H raw7687step1 = injectiveMoment H raw7687step2 := by
      have hz : ∀ j, raw7687step1 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7687step2 = (fun i j => raw7687step1 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7687step1 permutation27 hz
    injectiveMoment H raw7687step2 = injectiveMoment H raw7687step3 := by
      have heq : raw7687step3 = (fun i j => raw7687step2 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7687step2 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7688 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![-1, 1]]

def raw7688step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7688 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7688 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7688 = injectiveMoment H raw7688step0 := by
      have heq : raw7688step0 = (fun i j => raw7688 (permutation92 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7688 permutation92 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7689 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![0, 0], ![-1, 1]]

def raw7689step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![-1, 1]]

def raw7689step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7689 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7689 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7689 = injectiveMoment H raw7689step0 := by
      have hz : ∀ j, raw7689 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7689step0 = (fun i j => raw7689 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7689 permutation258 hz
    injectiveMoment H raw7689step0 = injectiveMoment H raw7689step1 := by
      have heq : raw7689step1 = (fun i j => raw7689step0 (permutation92 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7689step0 permutation92 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7690 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![3, -3], ![-1, 1]]

def raw7690step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7690 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7690 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw7690 = injectiveMoment H raw7690step0 := by
      have heq : raw7690step0 = (fun i j => raw7690 (permutation21 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7690 permutation21 permutation2
    _ = injectiveMoment H node26 := by rfl

def raw7691 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![3, -3], ![0, 0], ![-1, 1]]

def raw7691step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![3, -3], ![-1, 1]]

def raw7691step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7691 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7691 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw7691 = injectiveMoment H raw7691step0 := by
      have hz : ∀ j, raw7691 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7691step0 = (fun i j => raw7691 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7691 permutation104 hz
    injectiveMoment H raw7691step0 = injectiveMoment H raw7691step1 := by
      have heq : raw7691step1 = (fun i j => raw7691step0 (permutation21 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7691step0 permutation21 permutation2
    _ = injectiveMoment H node26 := by rfl

def raw7692 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![0, 0], ![2, -2], ![1, -1]]

def raw7692step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![2, -2], ![1, -1]]

def raw7692step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7692step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7692 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7692 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7692 = injectiveMoment H raw7692step0 := by
      have hz : ∀ j, raw7692 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw7692step0 = (fun i j => raw7692 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7692 permutation241 hz
    injectiveMoment H raw7692step0 = injectiveMoment H raw7692step1 := by
      have hz : ∀ j, raw7692step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw7692step1 = (fun i j => raw7692step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7692step0 permutation57 hz
    injectiveMoment H raw7692step1 = injectiveMoment H raw7692step2 := by
      have heq : raw7692step2 = (fun i j => raw7692step1 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7692step1 permutation16 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7693 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![2, -2]]

def raw7693step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7693step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7693 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7693 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7693 = injectiveMoment H raw7693step0 := by
      have hz : ∀ j, raw7693 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw7693step0 = (fun i j => raw7693 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7693 permutation57 hz
    injectiveMoment H raw7693step0 = injectiveMoment H raw7693step1 := by
      have heq : raw7693step1 = (fun i j => raw7693step0 (permutation15 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7693step0 permutation15 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7694 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![2, -2], ![0, 0]]

def raw7694step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![2, -2]]

def raw7694step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw7694step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7694 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7694 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7694 = injectiveMoment H raw7694step0 := by
      have hz : ∀ j, raw7694 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7694step0 = (fun i j => raw7694 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7694 permutation308 hz
    injectiveMoment H raw7694step0 = injectiveMoment H raw7694step1 := by
      have hz : ∀ j, raw7694step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw7694step1 = (fun i j => raw7694step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7694step0 permutation57 hz
    injectiveMoment H raw7694step1 = injectiveMoment H raw7694step2 := by
      have heq : raw7694step2 = (fun i j => raw7694step1 (permutation15 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7694step1 permutation15 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7695 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![2, -2], ![1, -1]]

def raw7695step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw7695step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7695 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7695 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7695 = injectiveMoment H raw7695step0 := by
      have hz : ∀ j, raw7695 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw7695step0 = (fun i j => raw7695 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7695 permutation57 hz
    injectiveMoment H raw7695step0 = injectiveMoment H raw7695step1 := by
      have heq : raw7695step1 = (fun i j => raw7695step0 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7695step0 permutation16 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7696 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw7696step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw7696step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7696 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7696 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7696 = injectiveMoment H raw7696step0 := by
      have hz : ∀ j, raw7696 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw7696step0 = (fun i j => raw7696 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7696 permutation202 hz
    injectiveMoment H raw7696step0 = injectiveMoment H raw7696step1 := by
      have heq : raw7696step1 = (fun i j => raw7696step0 (permutation145 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7696step0 permutation145 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7697 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw7697step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw7697step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7697 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7697 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7697 = injectiveMoment H raw7697step0 := by
      have hz : ∀ j, raw7697 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw7697step0 = (fun i j => raw7697 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7697 permutation202 hz
    injectiveMoment H raw7697step0 = injectiveMoment H raw7697step1 := by
      have heq : raw7697step1 = (fun i j => raw7697step0 (permutation122 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7697step0 permutation122 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7698 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![0, 0], ![0, 0], ![2, -2]]

def raw7698step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![0, 0], ![2, -2]]

def raw7698step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7698step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7698step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7698 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7698 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7698 = injectiveMoment H raw7698step0 := by
      have hz : ∀ j, raw7698 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7698step0 = (fun i j => raw7698 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7698 permutation258 hz
    injectiveMoment H raw7698step0 = injectiveMoment H raw7698step1 := by
      have hz : ∀ j, raw7698step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7698step1 = (fun i j => raw7698step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7698step0 permutation104 hz
    injectiveMoment H raw7698step1 = injectiveMoment H raw7698step2 := by
      have hz : ∀ j, raw7698step1 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw7698step2 = (fun i j => raw7698step1 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7698step1 permutation15 hz
    injectiveMoment H raw7698step2 = injectiveMoment H raw7698step3 := by
      have heq : raw7698step3 = (fun i j => raw7698step2 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7698step2 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7699 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![0, 0], ![2, -2]]

def raw7699step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7699step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7699step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7699 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7699 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7699 = injectiveMoment H raw7699step0 := by
      have hz : ∀ j, raw7699 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7699step0 = (fun i j => raw7699 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7699 permutation104 hz
    injectiveMoment H raw7699step0 = injectiveMoment H raw7699step1 := by
      have hz : ∀ j, raw7699step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw7699step1 = (fun i j => raw7699step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7699step0 permutation15 hz
    injectiveMoment H raw7699step1 = injectiveMoment H raw7699step2 := by
      have heq : raw7699step2 = (fun i j => raw7699step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7699step1 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7700 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![0, 0], ![2, -2], ![0, 0]]

def raw7700step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![0, 0], ![2, -2]]

def raw7700step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7700step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7700step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7700 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7700 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7700 = injectiveMoment H raw7700step0 := by
      have hz : ∀ j, raw7700 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7700step0 = (fun i j => raw7700 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7700 permutation308 hz
    injectiveMoment H raw7700step0 = injectiveMoment H raw7700step1 := by
      have hz : ∀ j, raw7700step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7700step1 = (fun i j => raw7700step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7700step0 permutation104 hz
    injectiveMoment H raw7700step1 = injectiveMoment H raw7700step2 := by
      have hz : ∀ j, raw7700step1 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw7700step2 = (fun i j => raw7700step1 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7700step1 permutation15 hz
    injectiveMoment H raw7700step2 = injectiveMoment H raw7700step3 := by
      have heq : raw7700step3 = (fun i j => raw7700step2 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7700step2 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7701 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]

def raw7701step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]

def raw7701step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7701 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7701 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7701 = injectiveMoment H raw7701step0 := by
      have hz : ∀ j, raw7701 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw7701step0 = (fun i j => raw7701 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7701 permutation202 hz
    injectiveMoment H raw7701step0 = injectiveMoment H raw7701step1 := by
      have heq : raw7701step1 = (fun i j => raw7701step0 (permutation139 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7701step0 permutation139 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7702 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![0, 0], ![1, -1]]

def raw7702step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![1, -1]]

def raw7702step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7702 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7702 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7702 = injectiveMoment H raw7702step0 := by
      have hz : ∀ j, raw7702 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7702step0 = (fun i j => raw7702 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7702 permutation258 hz
    injectiveMoment H raw7702step0 = injectiveMoment H raw7702step1 := by
      have hz : ∀ j, raw7702step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw7702step1 = (fun i j => raw7702step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7702step0 permutation57 hz
    _ = injectiveMoment H node65 := by rfl

def raw7703 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![1, -1]]

def raw7703step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7703 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7703 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7703 = injectiveMoment H raw7703step0 := by
      have hz : ∀ j, raw7703 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw7703step0 = (fun i j => raw7703 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7703 permutation57 hz
    _ = injectiveMoment H node65 := by rfl

def raw7704 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![1, -1], ![0, 0]]

def raw7704step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![1, -1]]

def raw7704step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7704 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7704 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7704 = injectiveMoment H raw7704step0 := by
      have hz : ∀ j, raw7704 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7704step0 = (fun i j => raw7704 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7704 permutation308 hz
    injectiveMoment H raw7704step0 = injectiveMoment H raw7704step1 := by
      have hz : ∀ j, raw7704step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw7704step1 = (fun i j => raw7704step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7704step0 permutation57 hz
    _ = injectiveMoment H node65 := by rfl

def raw7705 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7705step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7705step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7705 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7705 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7705 = injectiveMoment H raw7705step0 := by
      have hz : ∀ j, raw7705 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw7705step0 = (fun i j => raw7705 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7705 permutation15 hz
    injectiveMoment H raw7705step0 = injectiveMoment H raw7705step1 := by
      have heq : raw7705step1 = (fun i j => raw7705step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7705step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7706 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2], ![0, 0]]

def raw7706step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7706step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7706step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7706 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7706 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7706 = injectiveMoment H raw7706step0 := by
      have hz : ∀ j, raw7706 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7706step0 = (fun i j => raw7706 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7706 permutation128 hz
    injectiveMoment H raw7706step0 = injectiveMoment H raw7706step1 := by
      have hz : ∀ j, raw7706step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw7706step1 = (fun i j => raw7706step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7706step0 permutation15 hz
    injectiveMoment H raw7706step1 = injectiveMoment H raw7706step2 := by
      have heq : raw7706step2 = (fun i j => raw7706step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7706step1 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7707 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-1, 1], ![2, -2]]

def raw7707step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7707step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7707step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7707 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7707 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7707 = injectiveMoment H raw7707step0 := by
      have hz : ∀ j, raw7707 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw7707step0 = (fun i j => raw7707 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7707 permutation80 hz
    injectiveMoment H raw7707step0 = injectiveMoment H raw7707step1 := by
      have hz : ∀ j, raw7707step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw7707step1 = (fun i j => raw7707step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7707step0 permutation15 hz
    injectiveMoment H raw7707step1 = injectiveMoment H raw7707step2 := by
      have heq : raw7707step2 = (fun i j => raw7707step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7707step1 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7708 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![0, 0], ![1, -1]]

def raw7708step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![1, -1]]

def raw7708step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1]]

def raw7708step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical7708 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7708 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7708 = injectiveMoment H raw7708step0 := by
      have hz : ∀ j, raw7708 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7708step0 = (fun i j => raw7708 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7708 permutation104 hz
    injectiveMoment H raw7708step0 = injectiveMoment H raw7708step1 := by
      have hz : ∀ j, raw7708step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7708step1 = (fun i j => raw7708step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7708step0 permutation21 hz
    injectiveMoment H raw7708step1 = injectiveMoment H raw7708step2 := by
      have hz : ∀ j, raw7708step1 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw7708step2 = (fun i j => raw7708step1 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7708step1 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

def raw7709 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1]]

def raw7709step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical7709 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7709 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7709 = injectiveMoment H raw7709step0 := by
      have hz : ∀ j, raw7709 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw7709step0 = (fun i j => raw7709 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7709 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

def raw7710 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![-2, 2], ![2, -2]]

def raw7710step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw7710step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical7710 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7710 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7710 = injectiveMoment H raw7710step0 := by
      have hz : ∀ j, raw7710 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw7710step0 = (fun i j => raw7710 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7710 permutation57 hz
    injectiveMoment H raw7710step0 = injectiveMoment H raw7710step1 := by
      have heq : raw7710step1 = (fun i j => raw7710step0 (permutation21 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7710step0 permutation21 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw7711 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![-1, 1], ![0, 0], ![1, -1]]

def raw7711step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![1, -1], ![-1, 1], ![1, -1]]

def raw7711step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![1, -1]]

def raw7711step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7711 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7711 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7711 = injectiveMoment H raw7711step0 := by
      have hz : ∀ j, raw7711 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7711step0 = (fun i j => raw7711 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7711 permutation258 hz
    injectiveMoment H raw7711step0 = injectiveMoment H raw7711step1 := by
      have hz : ∀ j, raw7711step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw7711step1 = (fun i j => raw7711step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7711step0 permutation57 hz
    injectiveMoment H raw7711step1 = injectiveMoment H raw7711step2 := by
      have heq : raw7711step2 = (fun i j => raw7711step1 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7711step1 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
