import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8128 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 1, 1, -4]]

def raw8128step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 0, -1, -1], ![-2, -1, -1, 4]]

def raw8128step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical8128 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8128 = injectiveMoment H node2903 := by
  calc
    injectiveMoment H raw8128 = injectiveMoment H raw8128step0 := by
      have heq : raw8128step0 = -raw8128 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8128).symm
    injectiveMoment H raw8128step0 = injectiveMoment H raw8128step1 := by
      have heq : raw8128step1 = (fun i j => raw8128step0 (permutation379 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8128step0 permutation379 permutation9
    _ = injectiveMoment H node2903 := by rfl

def raw8129 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, 0, 2, -4]]

def raw8129step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, -1, 0, -1], ![-2, 0, -2, 4]]

def raw8129step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

theorem canonical8129 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8129 = injectiveMoment H node3109 := by
  calc
    injectiveMoment H raw8129 = injectiveMoment H raw8129step0 := by
      have heq : raw8129step0 = -raw8129 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8129).symm
    injectiveMoment H raw8129step0 = injectiveMoment H raw8129step1 := by
      have heq : raw8129step1 = (fun i j => raw8129step0 (permutation379 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8129step0 permutation379 permutation9
    _ = injectiveMoment H node3109 := by rfl

def raw8130 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, 0, -1, 1]]

def raw8130step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 0, 1, -1]]

def raw8130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -2, 4], ![0, 1, -1]]

def raw8130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical8130 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8130 = injectiveMoment H node437 := by
  calc
    injectiveMoment H raw8130 = injectiveMoment H raw8130step0 := by
      have heq : raw8130step0 = -raw8130 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8130).symm
    injectiveMoment H raw8130step0 = injectiveMoment H raw8130step1 := by
      have hz : ∀ i, raw8130step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8130step1 = (fun i j => raw8130step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8130step0 permutation9 hz
    injectiveMoment H raw8130step1 = injectiveMoment H raw8130step2 := by
      have heq : raw8130step2 = (fun i j => raw8130step1 (permutation113 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8130step1 permutation113 permutation3
    _ = injectiveMoment H node437 := by rfl

def raw8131 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 2, 1, -4]]

def raw8131step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![-1, -2, -1, 4]]

def raw8131step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical8131 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8131 = injectiveMoment H node2903 := by
  calc
    injectiveMoment H raw8131 = injectiveMoment H raw8131step0 := by
      have heq : raw8131step0 = -raw8131 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8131).symm
    injectiveMoment H raw8131step0 = injectiveMoment H raw8131step1 := by
      have heq : raw8131step1 = (fun i j => raw8131step0 (permutation380 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8131step0 permutation380 permutation15
    _ = injectiveMoment H node2903 := by rfl

def raw8132 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 1, 2, -4]]

def raw8132step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 2, -4]]

theorem canonical8132 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8132 = injectiveMoment H node3213 := by
  calc
    injectiveMoment H raw8132 = injectiveMoment H raw8132step0 := by
      have heq : raw8132step0 = (fun i j => raw8132 (permutation151 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8132 permutation151 permutation15
    _ = injectiveMoment H node3213 := by rfl

def raw8133 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, 1, -1], ![1, 0, 0, -1]]

def raw8133step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical8133 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8133 = injectiveMoment H node2645 := by
  calc
    injectiveMoment H raw8133 = injectiveMoment H raw8133step0 := by
      have heq : raw8133step0 = (fun i j => raw8133 (permutation118 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8133 permutation118 permutation14
    _ = injectiveMoment H node2645 := by rfl

def raw8134 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, 2, -2], ![1, 0, -1, 0]]

def raw8134step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical8134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8134 = injectiveMoment H node2447 := by
  calc
    injectiveMoment H raw8134 = injectiveMoment H raw8134step0 := by
      have heq : raw8134step0 = (fun i j => raw8134 (permutation116 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8134 permutation116 permutation13
    _ = injectiveMoment H node2447 := by rfl

def raw8135 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, 0, 2, -4]]

def raw8135step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![2, 0, 0, -2], ![-2, 0, -2, 4]]

def raw8135step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical8135 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8135 = injectiveMoment H node3101 := by
  calc
    injectiveMoment H raw8135 = injectiveMoment H raw8135step0 := by
      have heq : raw8135step0 = -raw8135 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8135).symm
    injectiveMoment H raw8135step0 = injectiveMoment H raw8135step1 := by
      have heq : raw8135step1 = (fun i j => raw8135step0 (permutation364 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8135step0 permutation364 permutation9
    _ = injectiveMoment H node3101 := by rfl

def raw8136 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, 0, 0]]

def raw8136step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2]]

def raw8136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8136 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8136 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw8136 = injectiveMoment H raw8136step0 := by
      have hz : ∀ j, raw8136 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8136step0 = (fun i j => raw8136 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8136 permutation128 hz
    injectiveMoment H raw8136step0 = injectiveMoment H raw8136step1 := by
      have hz : ∀ i, raw8136step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8136step1 = (fun i j => raw8136step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8136step0 permutation9 hz
    _ = injectiveMoment H node230 := by rfl

def raw8137 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![0, 0, -1, 1]]

def raw8137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![0, -1, 1]]

def raw8137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical8137 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8137 = injectiveMoment H node708 := by
  calc
    injectiveMoment H raw8137 = injectiveMoment H raw8137step0 := by
      have hz : ∀ i, raw8137 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8137step0 = (fun i j => raw8137 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8137 permutation9 hz
    injectiveMoment H raw8137step0 = injectiveMoment H raw8137step1 := by
      have heq : raw8137step1 = (fun i j => raw8137step0 (permutation37 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8137step0 permutation37 permutation3
    _ = injectiveMoment H node708 := by rfl

def raw8138 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 1, 2, -4]]

def raw8138step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem canonical8138 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8138 = injectiveMoment H node3151 := by
  calc
    injectiveMoment H raw8138 = injectiveMoment H raw8138step0 := by
      have heq : raw8138step0 = (fun i j => raw8138 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8138 permutation258 permutation9
    _ = injectiveMoment H node3151 := by rfl

def raw8139 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8139step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![0, -2, -1, 3], ![0, 0, 1, -1]]

def raw8139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-2, -1, 3], ![0, 1, -1]]

def raw8139step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical8139 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8139 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw8139 = injectiveMoment H raw8139step0 := by
      have heq : raw8139step0 = -raw8139 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8139).symm
    injectiveMoment H raw8139step0 = injectiveMoment H raw8139step1 := by
      have hz : ∀ i, raw8139step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8139step1 = (fun i j => raw8139step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8139step0 permutation9 hz
    injectiveMoment H raw8139step1 = injectiveMoment H raw8139step2 := by
      have heq : raw8139step2 = (fun i j => raw8139step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8139step1 permutation24 permutation3
    _ = injectiveMoment H node176 := by rfl

def raw8140 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 2, -4]]

def raw8140step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -2, -2, 4]]

def raw8140step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical8140 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8140 = injectiveMoment H node3102 := by
  calc
    injectiveMoment H raw8140 = injectiveMoment H raw8140step0 := by
      have heq : raw8140step0 = -raw8140 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8140).symm
    injectiveMoment H raw8140step0 = injectiveMoment H raw8140step1 := by
      have heq : raw8140step1 = (fun i j => raw8140step0 (permutation365 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8140step0 permutation365 permutation15
    _ = injectiveMoment H node3102 := by rfl

def raw8141 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def raw8141step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical8141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8141 = injectiveMoment H node2742 := by
  calc
    injectiveMoment H raw8141 = injectiveMoment H raw8141step0 := by
      have heq : raw8141step0 = (fun i j => raw8141 (permutation80 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8141 permutation80 permutation10
    _ = injectiveMoment H node2742 := by rfl

def raw8142 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![-1, 1, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8142step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical8142 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8142 = injectiveMoment H node2447 := by
  calc
    injectiveMoment H raw8142 = injectiveMoment H raw8142step0 := by
      have heq : raw8142step0 = (fun i j => raw8142 (permutation92 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8142 permutation92 permutation11
    _ = injectiveMoment H node2447 := by rfl

def raw8143 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8143step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical8143 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8143 = injectiveMoment H node2632 := by
  calc
    injectiveMoment H raw8143 = injectiveMoment H raw8143step0 := by
      have heq : raw8143step0 = (fun i j => raw8143 (permutation94 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8143 permutation94 permutation12
    _ = injectiveMoment H node2632 := by rfl

def raw8144 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8144step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical8144 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8144 = injectiveMoment H node2645 := by
  calc
    injectiveMoment H raw8144 = injectiveMoment H raw8144step0 := by
      have heq : raw8144step0 = (fun i j => raw8144 (permutation94 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8144 permutation94 permutation12
    _ = injectiveMoment H node2645 := by rfl

def raw8145 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![-1, 2, -2, 1], ![1, 0, 0, -1]]

def raw8145step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![1, 1, -2, 0], ![1, -1, 1, -1]]

def raw8145step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical8145 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8145 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw8145 = injectiveMoment H raw8145step0 := by
      have heq : raw8145step0 = raw8145.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8145).symm
    injectiveMoment H raw8145step0 = injectiveMoment H raw8145step1 := by
      have heq : raw8145step1 = (fun i j => raw8145step0 (permutation29 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8145step0 permutation29 permutation19
    _ = injectiveMoment H node1110 := by rfl

def raw8146 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, -3, 2], ![1, 0, 0, -1]]

def raw8146step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 3, -2], ![-1, 0, 0, 1]]

def raw8146step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

theorem canonical8146 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8146 = injectiveMoment H node2782 := by
  calc
    injectiveMoment H raw8146 = injectiveMoment H raw8146step0 := by
      have heq : raw8146step0 = -raw8146 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8146).symm
    injectiveMoment H raw8146step0 = injectiveMoment H raw8146step1 := by
      have heq : raw8146step1 = (fun i j => raw8146step0 (permutation135 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8146step0 permutation135 permutation9
    _ = injectiveMoment H node2782 := by rfl

def raw8147 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![0, 0, 0, 0]]

def raw8147step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -2, 3, -1], ![0, 0, 0, 0]]

def raw8147step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -2, 3, -1]]

def raw8147step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 3, -1]]

def raw8147step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical8147 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8147 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw8147 = injectiveMoment H raw8147step0 := by
      have heq : raw8147step0 = -raw8147 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8147).symm
    injectiveMoment H raw8147step0 = injectiveMoment H raw8147step1 := by
      have hz : ∀ j, raw8147step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8147step1 = (fun i j => raw8147step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8147step0 permutation128 hz
    injectiveMoment H raw8147step1 = injectiveMoment H raw8147step2 := by
      have hz : ∀ i, raw8147step1 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8147step2 = (fun i j => raw8147step1 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8147step1 permutation9 hz
    injectiveMoment H raw8147step2 = injectiveMoment H raw8147step3 := by
      have heq : raw8147step3 = (fun i j => raw8147step2 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8147step2 permutation30 permutation4
    _ = injectiveMoment H node176 := by rfl

def raw8148 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![-1, 1, 0, 0], ![1, 0, 0, -1]]

def raw8148step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical8148 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8148 = injectiveMoment H node2744 := by
  calc
    injectiveMoment H raw8148 = injectiveMoment H raw8148step0 := by
      have heq : raw8148step0 = (fun i j => raw8148 (permutation118 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8148 permutation118 permutation12
    _ = injectiveMoment H node2744 := by rfl

def raw8149 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![0, 0, 0, 0]]

def raw8149step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1]]

def raw8149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw8149step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8149 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8149 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw8149 = injectiveMoment H raw8149step0 := by
      have hz : ∀ j, raw8149 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8149step0 = (fun i j => raw8149 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8149 permutation128 hz
    injectiveMoment H raw8149step0 = injectiveMoment H raw8149step1 := by
      have hz : ∀ i, raw8149step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8149step1 = (fun i j => raw8149step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8149step0 permutation9 hz
    injectiveMoment H raw8149step1 = injectiveMoment H raw8149step2 := by
      have heq : raw8149step2 = (fun i j => raw8149step1 (permutation10 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8149step1 permutation10 permutation4
    _ = injectiveMoment H node230 := by rfl

def raw8150 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![1, 0, 0, -1]]

def raw8150step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical8150 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8150 = injectiveMoment H node2632 := by
  calc
    injectiveMoment H raw8150 = injectiveMoment H raw8150step0 := by
      have heq : raw8150step0 = (fun i j => raw8150 (permutation118 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8150 permutation118 permutation12
    _ = injectiveMoment H node2632 := by rfl

def raw8151 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-1, 1, 0, 0], ![1, 0, -1, 0]]

def raw8151step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![1, -1, 0, 0], ![-1, 0, 1, 0]]

def raw8151step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical8151 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8151 = injectiveMoment H node2725 := by
  calc
    injectiveMoment H raw8151 = injectiveMoment H raw8151step0 := by
      have heq : raw8151step0 = -raw8151 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8151).symm
    injectiveMoment H raw8151step0 = injectiveMoment H raw8151step1 := by
      have heq : raw8151step1 = (fun i j => raw8151step0 (permutation54 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8151step0 permutation54 permutation28
    _ = injectiveMoment H node2725 := by rfl

def raw8152 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, 0, 0, 0]]

def raw8152step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 0, 0]]

def raw8152step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 1, 0]]

def raw8152step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]

def raw8152step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical8152 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8152 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw8152 = injectiveMoment H raw8152step0 := by
      have heq : raw8152step0 = -raw8152 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8152).symm
    injectiveMoment H raw8152step0 = injectiveMoment H raw8152step1 := by
      have hz : ∀ j, raw8152step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8152step1 = (fun i j => raw8152step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8152step0 permutation128 hz
    injectiveMoment H raw8152step1 = injectiveMoment H raw8152step2 := by
      have hz : ∀ i, raw8152step1 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8152step2 = (fun i j => raw8152step1 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8152step1 permutation9 hz
    injectiveMoment H raw8152step2 = injectiveMoment H raw8152step3 := by
      have heq : raw8152step3 = (fun i j => raw8152step2 (permutation12 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8152step2 permutation12 permutation8
    _ = injectiveMoment H node287 := by rfl

def raw8153 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![0, 0, -1, 1]]

def raw8153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1]]

def raw8153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8153 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8153 = injectiveMoment H node711 := by
  calc
    injectiveMoment H raw8153 = injectiveMoment H raw8153step0 := by
      have hz : ∀ i, raw8153 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8153step0 = (fun i j => raw8153 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8153 permutation9 hz
    injectiveMoment H raw8153step0 = injectiveMoment H raw8153step1 := by
      have heq : raw8153step1 = (fun i j => raw8153step0 (permutation51 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8153step0 permutation51 permutation3
    _ = injectiveMoment H node711 := by rfl

def raw8154 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![0, 0, 0, 0]]

def raw8154step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, -2, 2, 0], ![0, 0, 0, 0]]

def raw8154step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -1, 1], ![0, -2, 2, 0]]

def raw8154step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-2, 2, 0]]

def raw8154step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical8154 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8154 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw8154 = injectiveMoment H raw8154step0 := by
      have heq : raw8154step0 = -raw8154 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8154).symm
    injectiveMoment H raw8154step0 = injectiveMoment H raw8154step1 := by
      have hz : ∀ j, raw8154step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw8154step1 = (fun i j => raw8154step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8154step0 permutation27 hz
    injectiveMoment H raw8154step1 = injectiveMoment H raw8154step2 := by
      have hz : ∀ i, raw8154step1 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8154step2 = (fun i j => raw8154step1 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8154step1 permutation9 hz
    injectiveMoment H raw8154step2 = injectiveMoment H raw8154step3 := by
      have heq : raw8154step3 = (fun i j => raw8154step2 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8154step2 permutation4 permutation8
    _ = injectiveMoment H node62 := by rfl

def raw8155 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 0, 2, -2], ![0, 2, -3, 1]]

def raw8155step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 2, -1, -1], ![0, 0, -2, 2], ![0, -2, 3, -1]]

def raw8155step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -2, 2], ![-2, 3, -1]]

def raw8155step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

theorem canonical8155 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8155 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw8155 = injectiveMoment H raw8155step0 := by
      have heq : raw8155step0 = -raw8155 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8155).symm
    injectiveMoment H raw8155step0 = injectiveMoment H raw8155step1 := by
      have hz : ∀ i, raw8155step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8155step1 = (fun i j => raw8155step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8155step0 permutation9 hz
    injectiveMoment H raw8155step1 = injectiveMoment H raw8155step2 := by
      have heq : raw8155step2 = (fun i j => raw8155step1 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8155step1 permutation8 permutation4
    _ = injectiveMoment H node36 := by rfl

def raw8156 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 1, -3, 2], ![0, 1, 2, -3]]

def raw8156step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical8156 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8156 = injectiveMoment H node43 := by
  calc
    injectiveMoment H raw8156 = injectiveMoment H raw8156step0 := by
      have hz : ∀ i, raw8156 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8156step0 = (fun i j => raw8156 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8156 permutation9 hz
    _ = injectiveMoment H node43 := by rfl

def raw8157 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2]]

def raw8157step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical8157 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8157 = injectiveMoment H node44 := by
  calc
    injectiveMoment H raw8157 = injectiveMoment H raw8157step0 := by
      have hz : ∀ i, raw8157 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8157step0 = (fun i j => raw8157 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8157 permutation9 hz
    _ = injectiveMoment H node44 := by rfl

def raw8158 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 1, -1, 0], ![-1, 1, 1, -1], ![1, 0, -1, 0]]

def raw8158step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical8158 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8158 = injectiveMoment H node1117 := by
  calc
    injectiveMoment H raw8158 = injectiveMoment H raw8158step0 := by
      have heq : raw8158step0 = (fun i j => raw8158 (permutation24 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8158 permutation24 permutation28
    _ = injectiveMoment H node1117 := by rfl

def raw8159 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, -1, 1]]

def raw8159step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![0, -1, 1]]

def raw8159step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8159 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8159 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw8159 = injectiveMoment H raw8159step0 := by
      have hz : ∀ i, raw8159 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8159step0 = (fun i j => raw8159 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8159 permutation9 hz
    injectiveMoment H raw8159step0 = injectiveMoment H raw8159step1 := by
      have heq : raw8159step1 = (fun i j => raw8159step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8159step0 permutation13 permutation3
    _ = injectiveMoment H node230 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
