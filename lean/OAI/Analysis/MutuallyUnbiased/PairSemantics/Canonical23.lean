import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical736 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw736 = injectiveMoment H node1431 := by
  rfl

def raw737 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

theorem canonical737 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw737 = injectiveMoment H node367 := by
  rfl

def raw738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem canonical738 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw738 = injectiveMoment H node1432 := by
  rfl

def raw739 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

theorem canonical739 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw739 = injectiveMoment H node368 := by
  rfl

def raw740 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

theorem canonical740 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw740 = injectiveMoment H node369 := by
  rfl

def raw741 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]

theorem canonical741 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw741 = injectiveMoment H node105 := by
  rfl

def raw742 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical742 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw742 = injectiveMoment H node370 := by
  rfl

def raw743 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical743 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw743 = injectiveMoment H node371 := by
  rfl

def raw744 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

theorem canonical744 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw744 = injectiveMoment H node106 := by
  rfl

def raw745 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -2, 1], ![1, 3, -4]]

def raw745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical745 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw745 = injectiveMoment H node370 := by
  calc
    injectiveMoment H raw745 = injectiveMoment H raw745step0 := by
      have heq : raw745step0 = (fun i j => raw745 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw745 permutation35 permutation3
    _ = injectiveMoment H node370 := by rfl

def raw746 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical746 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw746 = injectiveMoment H node372 := by
  rfl

def raw747 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical747 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw747 = injectiveMoment H node872 := by
  calc
    injectiveMoment H raw747 = injectiveMoment H raw747step0 := by
      have heq : raw747step0 = -raw747 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw747).symm
    injectiveMoment H raw747step0 = injectiveMoment H raw747step1 := by
      have heq : raw747step1 = (fun i j => raw747step0 (permutation55 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw747step0 permutation55 permutation6
    _ = injectiveMoment H node872 := by rfl

def raw748 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]

def raw748step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, -1, 3]]

def raw748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical748 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw748 = injectiveMoment H node263 := by
  calc
    injectiveMoment H raw748 = injectiveMoment H raw748step0 := by
      have heq : raw748step0 = -raw748 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw748).symm
    injectiveMoment H raw748step0 = injectiveMoment H raw748step1 := by
      have heq : raw748step1 = (fun i j => raw748step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw748step0 permutation28 permutation5
    _ = injectiveMoment H node263 := by rfl

def raw749 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]

def raw749step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]

def raw749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical749 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw749 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw749 = injectiveMoment H raw749step0 := by
      have heq : raw749step0 = -raw749 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw749).symm
    injectiveMoment H raw749step0 = injectiveMoment H raw749step1 := by
      have heq : raw749step1 = (fun i j => raw749step0 (permutation12 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw749step0 permutation12 permutation6
    _ = injectiveMoment H node272 := by rfl

def raw750 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]

def raw750step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical750 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw750 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw750 = injectiveMoment H raw750step0 := by
      have heq : raw750step0 = -raw750 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw750).symm
    injectiveMoment H raw750step0 = injectiveMoment H raw750step1 := by
      have heq : raw750step1 = (fun i j => raw750step0 (permutation11 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw750step0 permutation11 permutation6
    _ = injectiveMoment H node261 := by rfl

def raw751 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical751 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw751 = injectiveMoment H node107 := by
  rfl

def raw752 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw752step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical752 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw752 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw752 = injectiveMoment H raw752step0 := by
      have hz : ∀ j, raw752 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw752step0 = (fun i j => raw752 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw752 permutation57 hz
    injectiveMoment H raw752step0 = injectiveMoment H raw752step1 := by
      have heq : raw752step1 = (fun i j => raw752step0 (permutation26 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw752step0 permutation26 permutation6
    _ = injectiveMoment H node226 := by rfl

def raw753 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical753 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw753 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw753 = injectiveMoment H raw753step0 := by
      have heq : raw753step0 = -raw753 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw753).symm
    injectiveMoment H raw753step0 = injectiveMoment H raw753step1 := by
      have hz : ∀ j, raw753step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw753step1 = (fun i j => raw753step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw753step0 permutation57 hz
    injectiveMoment H raw753step1 = injectiveMoment H raw753step2 := by
      have heq : raw753step2 = (fun i j => raw753step1 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw753step1 permutation11 permutation8
    _ = injectiveMoment H node181 := by rfl

def raw754 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw754step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical754 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw754 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw754 = injectiveMoment H raw754step0 := by
      have heq : raw754step0 = -raw754 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw754).symm
    injectiveMoment H raw754step0 = injectiveMoment H raw754step1 := by
      have hz : ∀ j, raw754step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw754step1 = (fun i j => raw754step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw754step0 permutation57 hz
    injectiveMoment H raw754step1 = injectiveMoment H raw754step2 := by
      have heq : raw754step2 = (fun i j => raw754step1 (permutation13 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw754step1 permutation13 permutation8
    _ = injectiveMoment H node185 := by rfl

def raw755 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]

def raw755step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 0, 3], ![1, 0, 1, -2], ![2, 0, -1, -1]]

def raw755step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]

def raw755step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical755 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw755 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw755 = injectiveMoment H raw755step0 := by
      have heq : raw755step0 = raw755.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw755).symm
    injectiveMoment H raw755step0 = injectiveMoment H raw755step1 := by
      have hz : ∀ i, raw755step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw755step1 = (fun i j => raw755step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw755step0 permutation15 hz
    injectiveMoment H raw755step1 = injectiveMoment H raw755step2 := by
      have heq : raw755step2 = (fun i j => raw755step1 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw755step1 permutation7 permutation6
    _ = injectiveMoment H node63 := by rfl

def raw756 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw756step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def raw756step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical756 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw756 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw756 = injectiveMoment H raw756step0 := by
      have hz : ∀ j, raw756 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw756step0 = (fun i j => raw756 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw756 permutation57 hz
    injectiveMoment H raw756step0 = injectiveMoment H raw756step1 := by
      have heq : raw756step1 = (fun i j => raw756step0 (permutation18 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw756step0 permutation18 permutation6
    _ = injectiveMoment H node229 := by rfl

def raw757 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]

def raw757step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]

def raw757step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical757 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw757 = injectiveMoment H node43 := by
  calc
    injectiveMoment H raw757 = injectiveMoment H raw757step0 := by
      have hz : ∀ j, raw757 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw757step0 = (fun i j => raw757 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw757 permutation15 hz
    injectiveMoment H raw757step0 = injectiveMoment H raw757step1 := by
      have heq : raw757step1 = (fun i j => raw757step0 (permutation5 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw757step0 permutation5 permutation5
    _ = injectiveMoment H node43 := by rfl

def raw758 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def raw758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical758 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw758 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw758 = injectiveMoment H raw758step0 := by
      have heq : raw758step0 = -raw758 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw758).symm
    injectiveMoment H raw758step0 = injectiveMoment H raw758step1 := by
      have hz : ∀ j, raw758step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw758step1 = (fun i j => raw758step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw758step0 permutation57 hz
    injectiveMoment H raw758step1 = injectiveMoment H raw758step2 := by
      have heq : raw758step2 = (fun i j => raw758step1 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw758step1 permutation9 permutation8
    _ = injectiveMoment H node176 := by rfl

def raw759 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]

def raw759step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 0, 0], ![-1, -1, 2], ![-2, 2, 0]]

def raw759step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]

def raw759step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

theorem canonical759 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw759 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw759 = injectiveMoment H raw759step0 := by
      have heq : raw759step0 = -raw759 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw759).symm
    injectiveMoment H raw759step0 = injectiveMoment H raw759step1 := by
      have hz : ∀ j, raw759step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw759step1 = (fun i j => raw759step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw759step0 permutation15 hz
    injectiveMoment H raw759step1 = injectiveMoment H raw759step2 := by
      have heq : raw759step2 = (fun i j => raw759step1 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw759step1 permutation4 permutation8
    _ = injectiveMoment H node36 := by rfl

def raw760 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]

def raw760step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical760 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw760 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw760 = injectiveMoment H raw760step0 := by
      have hz : ∀ j, raw760 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw760step0 = (fun i j => raw760 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw760 permutation80 hz
    injectiveMoment H raw760step0 = injectiveMoment H raw760step1 := by
      have heq : raw760step1 = (fun i j => raw760step0 (permutation26 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw760step0 permutation26 permutation6
    _ = injectiveMoment H node226 := by rfl

def raw761 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]

def raw761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1]]

def raw761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical761 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw761 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw761 = injectiveMoment H raw761step0 := by
      have heq : raw761step0 = -raw761 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw761).symm
    injectiveMoment H raw761step0 = injectiveMoment H raw761step1 := by
      have hz : ∀ j, raw761step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw761step1 = (fun i j => raw761step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw761step0 permutation80 hz
    injectiveMoment H raw761step1 = injectiveMoment H raw761step2 := by
      have heq : raw761step2 = (fun i j => raw761step1 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw761step1 permutation11 permutation8
    _ = injectiveMoment H node181 := by rfl

def raw762 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]

def raw762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![-2, 2, 0]]

def raw762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical762 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw762 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw762 = injectiveMoment H raw762step0 := by
      have heq : raw762step0 = -raw762 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw762).symm
    injectiveMoment H raw762step0 = injectiveMoment H raw762step1 := by
      have hz : ∀ j, raw762step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw762step1 = (fun i j => raw762step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw762step0 permutation80 hz
    injectiveMoment H raw762step1 = injectiveMoment H raw762step2 := by
      have heq : raw762step2 = (fun i j => raw762step1 (permutation13 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw762step1 permutation13 permutation8
    _ = injectiveMoment H node185 := by rfl

def raw763 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]

def raw763step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 0, 3], ![1, 1, 0, -2], ![2, -1, 0, -1]]

def raw763step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]

def raw763step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical763 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw763 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw763 = injectiveMoment H raw763step0 := by
      have heq : raw763step0 = raw763.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw763).symm
    injectiveMoment H raw763step0 = injectiveMoment H raw763step1 := by
      have hz : ∀ i, raw763step0 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw763step1 = (fun i j => raw763step0 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw763step0 permutation21 hz
    injectiveMoment H raw763step1 = injectiveMoment H raw763step2 := by
      have heq : raw763step2 = (fun i j => raw763step1 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw763step1 permutation7 permutation6
    _ = injectiveMoment H node63 := by rfl

def raw764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical764 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw764 = injectiveMoment H node1433 := by
  rfl

def raw765 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

theorem canonical765 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw765 = injectiveMoment H node373 := by
  rfl

def raw766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical766 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw766 = injectiveMoment H node1434 := by
  rfl

def raw767 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

theorem canonical767 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw767 = injectiveMoment H node374 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
