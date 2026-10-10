import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5664 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5664step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5664step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

theorem canonical5664 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5664 = injectiveMoment H node1221 := by
  calc
    injectiveMoment H raw5664 = injectiveMoment H raw5664step0 := by
      have hz : ∀ j, raw5664 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw5664step0 = (fun i j => raw5664 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5664 permutation57 hz
    injectiveMoment H raw5664step0 = injectiveMoment H raw5664step1 := by
      have heq : raw5664step1 = (fun i j => raw5664step0 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5664step0 permutation11 permutation11
    _ = injectiveMoment H node1221 := by rfl

def raw5665 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, 2, -1, -2]]

def raw5665step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 0, 2], ![0, 0, 1, -1], ![3, 0, -1, -2]]

def raw5665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![3, -1, -2]]

def raw5665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical5665 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5665 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw5665 = injectiveMoment H raw5665step0 := by
      have heq : raw5665step0 = raw5665.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5665).symm
    injectiveMoment H raw5665step0 = injectiveMoment H raw5665step1 := by
      have hz : ∀ i, raw5665step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw5665step1 = (fun i j => raw5665step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5665step0 permutation15 hz
    injectiveMoment H raw5665step1 = injectiveMoment H raw5665step2 := by
      have heq : raw5665step2 = (fun i j => raw5665step1 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5665step1 permutation27 permutation6
    _ = injectiveMoment H node272 := by rfl

def raw5666 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 0, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw5666step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![0, 0, -1, 1], ![3, 0, -1, -2]]

def raw5666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![3, -1, -2]]

def raw5666step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5666 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5666 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw5666 = injectiveMoment H raw5666step0 := by
      have heq : raw5666step0 = raw5666.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5666).symm
    injectiveMoment H raw5666step0 = injectiveMoment H raw5666step1 := by
      have hz : ∀ i, raw5666step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw5666step1 = (fun i j => raw5666step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5666step0 permutation15 hz
    injectiveMoment H raw5666step1 = injectiveMoment H raw5666step2 := by
      have heq : raw5666step2 = (fun i j => raw5666step1 (permutation30 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5666step1 permutation30 permutation8
    _ = injectiveMoment H node185 := by rfl

def raw5667 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 0, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw5667step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![0, 0, 1, -1], ![3, 0, -3, 0]]

def raw5667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 1, -1], ![3, -3, 0]]

def raw5667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

theorem canonical5667 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5667 = injectiveMoment H node292 := by
  calc
    injectiveMoment H raw5667 = injectiveMoment H raw5667step0 := by
      have heq : raw5667step0 = raw5667.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5667).symm
    injectiveMoment H raw5667step0 = injectiveMoment H raw5667step1 := by
      have hz : ∀ i, raw5667step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw5667step1 = (fun i j => raw5667step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5667step0 permutation15 hz
    injectiveMoment H raw5667step1 = injectiveMoment H raw5667step2 := by
      have heq : raw5667step2 = (fun i j => raw5667step1 (permutation24 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5667step1 permutation24 permutation7
    _ = injectiveMoment H node292 := by rfl

def raw5668 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5668step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5668step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

theorem canonical5668 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5668 = injectiveMoment H node1221 := by
  calc
    injectiveMoment H raw5668 = injectiveMoment H raw5668step0 := by
      have hz : ∀ j, raw5668 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5668step0 = (fun i j => raw5668 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5668 permutation80 hz
    injectiveMoment H raw5668step0 = injectiveMoment H raw5668step1 := by
      have heq : raw5668step1 = (fun i j => raw5668step0 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5668step0 permutation11 permutation11
    _ = injectiveMoment H node1221 := by rfl

def raw5669 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 2, -1, -2]]

def raw5669step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 0, 2], ![0, 1, 0, -1], ![3, -1, 0, -2]]

def raw5669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![3, -1, -2]]

def raw5669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical5669 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5669 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw5669 = injectiveMoment H raw5669step0 := by
      have heq : raw5669step0 = raw5669.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5669).symm
    injectiveMoment H raw5669step0 = injectiveMoment H raw5669step1 := by
      have hz : ∀ i, raw5669step0 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw5669step1 = (fun i j => raw5669step0 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5669step0 permutation21 hz
    injectiveMoment H raw5669step1 = injectiveMoment H raw5669step2 := by
      have heq : raw5669step2 = (fun i j => raw5669step1 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5669step1 permutation27 permutation6
    _ = injectiveMoment H node272 := by rfl

def raw5670 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical5670 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5670 = injectiveMoment H node2420 := by
  rfl

def raw5671 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical5671 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5671 = injectiveMoment H node2421 := by
  rfl

def raw5672 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical5672 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5672 = injectiveMoment H node2422 := by
  rfl

def raw5673 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical5673 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5673 = injectiveMoment H node2423 := by
  rfl

def raw5674 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -2, -1]]

def raw5674step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 0, 2], ![0, 1, 1, -2], ![3, -1, -1, -1]]

def raw5674step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -2, 0]]

theorem canonical5674 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5674 = injectiveMoment H node967 := by
  calc
    injectiveMoment H raw5674 = injectiveMoment H raw5674step0 := by
      have heq : raw5674step0 = raw5674.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5674).symm
    injectiveMoment H raw5674step0 = injectiveMoment H raw5674step1 := by
      have heq : raw5674step1 = (fun i j => raw5674step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5674step0 permutation27 permutation18
    _ = injectiveMoment H node967 := by rfl

def raw5675 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical5675 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5675 = injectiveMoment H node2424 := by
  rfl

def raw5676 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5676step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical5676 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5676 = injectiveMoment H node2704 := by
  calc
    injectiveMoment H raw5676 = injectiveMoment H raw5676step0 := by
      have heq : raw5676step0 = (fun i j => raw5676 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5676 permutation41 permutation11
    _ = injectiveMoment H node2704 := by rfl

def raw5677 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw5677step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical5677 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5677 = injectiveMoment H node1202 := by
  calc
    injectiveMoment H raw5677 = injectiveMoment H raw5677step0 := by
      have heq : raw5677step0 = (fun i j => raw5677 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5677 permutation11 permutation11
    _ = injectiveMoment H node1202 := by rfl

def raw5678 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw5678step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical5678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5678 = injectiveMoment H node2704 := by
  calc
    injectiveMoment H raw5678 = injectiveMoment H raw5678step0 := by
      have heq : raw5678step0 = (fun i j => raw5678 (permutation47 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5678 permutation47 permutation11
    _ = injectiveMoment H node2704 := by rfl

def raw5679 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw5679step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

theorem canonical5679 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5679 = injectiveMoment H node2708 := by
  calc
    injectiveMoment H raw5679 = injectiveMoment H raw5679step0 := by
      have heq : raw5679step0 = (fun i j => raw5679 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5679 permutation41 permutation11
    _ = injectiveMoment H node2708 := by rfl

def raw5680 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw5680step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![0, 1, 0, -1], ![3, -1, -1, -1]]

def raw5680step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical5680 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5680 = injectiveMoment H node969 := by
  calc
    injectiveMoment H raw5680 = injectiveMoment H raw5680step0 := by
      have heq : raw5680step0 = raw5680.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5680).symm
    injectiveMoment H raw5680step0 = injectiveMoment H raw5680step1 := by
      have heq : raw5680step1 = (fun i j => raw5680step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5680step0 permutation28 permutation24
    _ = injectiveMoment H node969 := by rfl

def raw5681 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical5681 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5681 = injectiveMoment H node801 := by
  rfl

def raw5682 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical5682 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5682 = injectiveMoment H node802 := by
  rfl

def raw5683 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw5683step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 2, 0], ![0, 1, -1, 0], ![3, -1, -1, -1]]

def raw5683step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical5683 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5683 = injectiveMoment H node974 := by
  calc
    injectiveMoment H raw5683 = injectiveMoment H raw5683step0 := by
      have heq : raw5683step0 = raw5683.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5683).symm
    injectiveMoment H raw5683step0 = injectiveMoment H raw5683step1 := by
      have heq : raw5683step1 = (fun i j => raw5683step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5683step0 permutation30 permutation30
    _ = injectiveMoment H node974 := by rfl

def raw5684 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw5684step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

theorem canonical5684 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5684 = injectiveMoment H node1221 := by
  calc
    injectiveMoment H raw5684 = injectiveMoment H raw5684step0 := by
      have heq : raw5684step0 = (fun i j => raw5684 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5684 permutation11 permutation11
    _ = injectiveMoment H node1221 := by rfl

def raw5685 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical5685 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5685 = injectiveMoment H node803 := by
  rfl

def raw5686 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![1, 2, -1, -2]]

def raw5686step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![3, -1, -2]]

def raw5686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical5686 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5686 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw5686 = injectiveMoment H raw5686step0 := by
      have heq : raw5686step0 = raw5686.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5686).symm
    injectiveMoment H raw5686step0 = injectiveMoment H raw5686step1 := by
      have heq : raw5686step1 = (fun i j => raw5686step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5686step0 permutation27 permutation6
    _ = injectiveMoment H node272 := by rfl

def raw5687 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical5687 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5687 = injectiveMoment H node804 := by
  rfl

def raw5688 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical5688 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5688 = injectiveMoment H node2427 := by
  rfl

def raw5689 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical5689 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5689 = injectiveMoment H node2428 := by
  rfl

def raw5690 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical5690 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5690 = injectiveMoment H node805 := by
  rfl

def raw5691 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw5691step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![0, 2, 0, -2], ![3, -2, -1, 0]]

def raw5691step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical5691 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5691 = injectiveMoment H node802 := by
  calc
    injectiveMoment H raw5691 = injectiveMoment H raw5691step0 := by
      have heq : raw5691step0 = raw5691.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5691).symm
    injectiveMoment H raw5691step0 = injectiveMoment H raw5691step1 := by
      have heq : raw5691step1 = (fun i j => raw5691step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5691step0 permutation28 permutation24
    _ = injectiveMoment H node802 := by rfl

def raw5692 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical5692 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5692 = injectiveMoment H node806 := by
  rfl

def raw5693 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical5693 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5693 = injectiveMoment H node807 := by
  rfl

def raw5694 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical5694 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5694 = injectiveMoment H node808 := by
  rfl

def raw5695 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![1, 2, -2, -1]]

def raw5695step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 2, -2], ![3, -2, -1]]

def raw5695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical5695 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5695 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw5695 = injectiveMoment H raw5695step0 := by
      have heq : raw5695step0 = raw5695.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5695).symm
    injectiveMoment H raw5695step0 = injectiveMoment H raw5695step1 := by
      have heq : raw5695step1 = (fun i j => raw5695step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5695step0 permutation27 permutation6
    _ = injectiveMoment H node177 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
