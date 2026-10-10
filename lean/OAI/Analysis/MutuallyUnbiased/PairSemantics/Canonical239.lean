import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7648 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-2, 2], ![1, -1], ![4, -4]]

def raw7648step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical7648 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7648 = injectiveMoment H node296 := by
  calc
    injectiveMoment H raw7648 = injectiveMoment H raw7648step0 := by
      have heq : raw7648step0 = (fun i j => raw7648 (permutation395 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7648 permutation395 permutation2
    _ = injectiveMoment H node296 := by rfl

def raw7649 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![3, -3]]

def raw7649step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical7649 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7649 = injectiveMoment H node380 := by
  calc
    injectiveMoment H raw7649 = injectiveMoment H raw7649step0 := by
      have heq : raw7649step0 = (fun i j => raw7649 (permutation395 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7649 permutation395 permutation2
    _ = injectiveMoment H node380 := by rfl

def raw7650 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![4, -4]]

def raw7650step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![4, -4]]

def raw7650step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7650 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7650 = injectiveMoment H node69 := by
  calc
    injectiveMoment H raw7650 = injectiveMoment H raw7650step0 := by
      have hz : ∀ j, raw7650 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7650step0 = (fun i j => raw7650 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7650 permutation258 hz
    injectiveMoment H raw7650step0 = injectiveMoment H raw7650step1 := by
      have heq : raw7650step1 = (fun i j => raw7650step0 (permutation128 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7650step0 permutation128 permutation2
    _ = injectiveMoment H node69 := by rfl

def raw7651 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]

def raw7651step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7651 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7651 = injectiveMoment H node383 := by
  calc
    injectiveMoment H raw7651 = injectiveMoment H raw7651step0 := by
      have heq : raw7651step0 = (fun i j => raw7651 (permutation395 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7651 permutation395 permutation2
    _ = injectiveMoment H node383 := by rfl

def raw7652 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]

def raw7652step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7652 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7652 = injectiveMoment H node716 := by
  calc
    injectiveMoment H raw7652 = injectiveMoment H raw7652step0 := by
      have heq : raw7652step0 = (fun i j => raw7652 (permutation294 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7652 permutation294 permutation2
    _ = injectiveMoment H node716 := by rfl

def raw7653 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]

def raw7653step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![3, -3]]

def raw7653step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7653step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7653 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7653 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw7653 = injectiveMoment H raw7653step0 := by
      have hz : ∀ j, raw7653 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7653step0 = (fun i j => raw7653 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7653 permutation258 hz
    injectiveMoment H raw7653step0 = injectiveMoment H raw7653step1 := by
      have hz : ∀ j, raw7653step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7653step1 = (fun i j => raw7653step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7653step0 permutation104 hz
    injectiveMoment H raw7653step1 = injectiveMoment H raw7653step2 := by
      have heq : raw7653step2 = (fun i j => raw7653step1 (permutation27 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7653step1 permutation27 permutation2
    _ = injectiveMoment H node26 := by rfl

def raw7654 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]

def raw7654step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw7654step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7654 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7654 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7654 = injectiveMoment H raw7654step0 := by
      have hz : ∀ j, raw7654 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw7654step0 = (fun i j => raw7654 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7654 permutation241 hz
    injectiveMoment H raw7654step0 = injectiveMoment H raw7654step1 := by
      have heq : raw7654step1 = (fun i j => raw7654step0 (permutation145 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7654step0 permutation145 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7655 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]

def raw7655step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw7655step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7655 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7655 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7655 = injectiveMoment H raw7655step0 := by
      have hz : ∀ j, raw7655 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw7655step0 = (fun i j => raw7655 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7655 permutation241 hz
    injectiveMoment H raw7655step0 = injectiveMoment H raw7655step1 := by
      have heq : raw7655step1 = (fun i j => raw7655step0 (permutation122 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7655step0 permutation122 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7656 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![3, -3]]

def raw7656step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7656step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7656 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7656 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw7656 = injectiveMoment H raw7656step0 := by
      have hz : ∀ j, raw7656 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7656step0 = (fun i j => raw7656 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7656 permutation104 hz
    injectiveMoment H raw7656step0 = injectiveMoment H raw7656step1 := by
      have heq : raw7656step1 = (fun i j => raw7656step0 (permutation27 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7656step0 permutation27 permutation2
    _ = injectiveMoment H node26 := by rfl

def raw7657 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]

def raw7657step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw7657step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7657 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7657 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7657 = injectiveMoment H raw7657step0 := by
      have hz : ∀ j, raw7657 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7657step0 = (fun i j => raw7657 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7657 permutation258 hz
    injectiveMoment H raw7657step0 = injectiveMoment H raw7657step1 := by
      have heq : raw7657step1 = (fun i j => raw7657step0 (permutation145 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7657step0 permutation145 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7658 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7658 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7658 = injectiveMoment H node1323 := by
  rfl

def raw7659 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw7659step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7659 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7659 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7659 = injectiveMoment H raw7659step0 := by
      have heq : raw7659step0 = (fun i j => raw7659 (permutation145 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7659 permutation145 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7660 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![0, 0]]

def raw7660step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw7660step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7660 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7660 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7660 = injectiveMoment H raw7660step0 := by
      have hz : ∀ j, raw7660 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7660step0 = (fun i j => raw7660 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7660 permutation308 hz
    injectiveMoment H raw7660step0 = injectiveMoment H raw7660step1 := by
      have heq : raw7660step1 = (fun i j => raw7660step0 (permutation145 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7660step0 permutation145 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7661 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw7661step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7661 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7661 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7661 = injectiveMoment H raw7661step0 := by
      have heq : raw7661step0 = (fun i j => raw7661 (permutation122 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7661 permutation122 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7662 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![0, 0]]

def raw7662step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw7662step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7662 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7662 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7662 = injectiveMoment H raw7662step0 := by
      have hz : ∀ j, raw7662 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7662step0 = (fun i j => raw7662 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7662 permutation308 hz
    injectiveMoment H raw7662step0 = injectiveMoment H raw7662step1 := by
      have heq : raw7662step1 = (fun i j => raw7662step0 (permutation122 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7662step0 permutation122 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7663 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7663step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7663 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7663 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw7663 = injectiveMoment H raw7663step0 := by
      have heq : raw7663step0 = (fun i j => raw7663 (permutation27 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7663 permutation27 permutation2
    _ = injectiveMoment H node26 := by rfl

def raw7664 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3], ![0, 0]]

def raw7664step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7664step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7664 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7664 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw7664 = injectiveMoment H raw7664step0 := by
      have hz : ∀ j, raw7664 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7664step0 = (fun i j => raw7664 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7664 permutation128 hz
    injectiveMoment H raw7664step0 = injectiveMoment H raw7664step1 := by
      have heq : raw7664step1 = (fun i j => raw7664step0 (permutation27 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7664step0 permutation27 permutation2
    _ = injectiveMoment H node26 := by rfl

def raw7665 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3], ![0, 0], ![0, 0]]

def raw7665step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3], ![0, 0]]

def raw7665step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7665step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7665 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7665 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw7665 = injectiveMoment H raw7665step0 := by
      have hz : ∀ j, raw7665 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7665step0 = (fun i j => raw7665 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7665 permutation308 hz
    injectiveMoment H raw7665step0 = injectiveMoment H raw7665step1 := by
      have hz : ∀ j, raw7665step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7665step1 = (fun i j => raw7665step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7665step0 permutation128 hz
    injectiveMoment H raw7665step1 = injectiveMoment H raw7665step2 := by
      have heq : raw7665step2 = (fun i j => raw7665step1 (permutation27 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7665step1 permutation27 permutation2
    _ = injectiveMoment H node26 := by rfl

def raw7666 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![3, -3]]

def raw7666step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw7666step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7666 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7666 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw7666 = injectiveMoment H raw7666step0 := by
      have hz : ∀ j, raw7666 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw7666step0 = (fun i j => raw7666 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7666 permutation80 hz
    injectiveMoment H raw7666step0 = injectiveMoment H raw7666step1 := by
      have heq : raw7666step1 = (fun i j => raw7666step0 (permutation27 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7666step0 permutation27 permutation2
    _ = injectiveMoment H node26 := by rfl

def raw7667 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![0, 0], ![2, -2]]

def raw7667step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![2, -2]]

def raw7667step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw7667step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7667step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7667 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7667 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7667 = injectiveMoment H raw7667step0 := by
      have hz : ∀ j, raw7667 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7667step0 = (fun i j => raw7667 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7667 permutation258 hz
    injectiveMoment H raw7667step0 = injectiveMoment H raw7667step1 := by
      have hz : ∀ j, raw7667step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7667step1 = (fun i j => raw7667step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7667step0 permutation104 hz
    injectiveMoment H raw7667step1 = injectiveMoment H raw7667step2 := by
      have hz : ∀ j, raw7667step1 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7667step2 = (fun i j => raw7667step1 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7667step1 permutation21 hz
    injectiveMoment H raw7667step2 = injectiveMoment H raw7667step3 := by
      have heq : raw7667step3 = (fun i j => raw7667step2 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7667step2 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7668 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]

def raw7668step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]

def raw7668step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7668 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7668 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7668 = injectiveMoment H raw7668step0 := by
      have hz : ∀ j, raw7668 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw7668step0 = (fun i j => raw7668 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7668 permutation241 hz
    injectiveMoment H raw7668step0 = injectiveMoment H raw7668step1 := by
      have hz : ∀ j, raw7668step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw7668step1 = (fun i j => raw7668step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7668step0 permutation80 hz
    _ = injectiveMoment H node65 := by rfl

def raw7669 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![2, -2]]

def raw7669step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw7669step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7669step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7669 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7669 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7669 = injectiveMoment H raw7669step0 := by
      have hz : ∀ j, raw7669 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7669step0 = (fun i j => raw7669 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7669 permutation104 hz
    injectiveMoment H raw7669step0 = injectiveMoment H raw7669step1 := by
      have hz : ∀ j, raw7669step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7669step1 = (fun i j => raw7669step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7669step0 permutation21 hz
    injectiveMoment H raw7669step1 = injectiveMoment H raw7669step2 := by
      have heq : raw7669step2 = (fun i j => raw7669step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7669step1 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7670 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]

def raw7670step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7670 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7670 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7670 = injectiveMoment H raw7670step0 := by
      have hz : ∀ j, raw7670 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw7670step0 = (fun i j => raw7670 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7670 permutation80 hz
    _ = injectiveMoment H node65 := by rfl

def raw7671 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw7671step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7671step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7671 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7671 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7671 = injectiveMoment H raw7671step0 := by
      have hz : ∀ j, raw7671 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7671step0 = (fun i j => raw7671 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7671 permutation21 hz
    injectiveMoment H raw7671step0 = injectiveMoment H raw7671step1 := by
      have heq : raw7671step1 = (fun i j => raw7671step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7671step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7672 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![2, -2], ![0, 0]]

def raw7672step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw7672step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw7672step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical7672 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7672 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7672 = injectiveMoment H raw7672step0 := by
      have hz : ∀ j, raw7672 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7672step0 = (fun i j => raw7672 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7672 permutation128 hz
    injectiveMoment H raw7672step0 = injectiveMoment H raw7672step1 := by
      have hz : ∀ j, raw7672step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7672step1 = (fun i j => raw7672step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7672step0 permutation21 hz
    injectiveMoment H raw7672step1 = injectiveMoment H raw7672step2 := by
      have heq : raw7672step2 = (fun i j => raw7672step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7672step1 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw7673 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![0, 0], ![2, -2]]

def raw7673step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]

def raw7673step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7673 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7673 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7673 = injectiveMoment H raw7673step0 := by
      have hz : ∀ j, raw7673 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7673step0 = (fun i j => raw7673 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7673 permutation258 hz
    injectiveMoment H raw7673step0 = injectiveMoment H raw7673step1 := by
      have heq : raw7673step1 = (fun i j => raw7673step0 (permutation139 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7673step0 permutation139 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7674 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]

def raw7674step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7674 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7674 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7674 = injectiveMoment H raw7674step0 := by
      have heq : raw7674step0 = (fun i j => raw7674 (permutation139 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7674 permutation139 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7675 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![2, -2]]

def raw7675step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]

def raw7675step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical7675 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7675 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw7675 = injectiveMoment H raw7675step0 := by
      have hz : ∀ j, raw7675 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw7675step0 = (fun i j => raw7675 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7675 permutation241 hz
    injectiveMoment H raw7675step0 = injectiveMoment H raw7675step1 := by
      have heq : raw7675step1 = (fun i j => raw7675step0 (permutation139 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7675step0 permutation139 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw7676 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![0, 0], ![1, -1]]

def raw7676step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![1, -1]]

def raw7676step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7676 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7676 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7676 = injectiveMoment H raw7676step0 := by
      have hz : ∀ j, raw7676 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7676step0 = (fun i j => raw7676 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7676 permutation258 hz
    injectiveMoment H raw7676step0 = injectiveMoment H raw7676step1 := by
      have hz : ∀ j, raw7676step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7676step1 = (fun i j => raw7676step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7676step0 permutation104 hz
    _ = injectiveMoment H node65 := by rfl

def raw7677 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![1, -1]]

def raw7677step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7677 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7677 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7677 = injectiveMoment H raw7677step0 := by
      have hz : ∀ j, raw7677 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7677step0 = (fun i j => raw7677 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7677 permutation104 hz
    _ = injectiveMoment H node65 := by rfl

def raw7678 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7678 = injectiveMoment H node65 := by
  rfl

def raw7679 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![0, 0]]

def raw7679step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical7679 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7679 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7679 = injectiveMoment H raw7679step0 := by
      have hz : ∀ j, raw7679 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7679step0 = (fun i j => raw7679 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7679 permutation128 hz
    _ = injectiveMoment H node65 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
