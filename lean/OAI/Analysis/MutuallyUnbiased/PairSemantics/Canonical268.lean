import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8576 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1]]

def raw8576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8576 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8576 = injectiveMoment H node2660 := by
  calc
    injectiveMoment H raw8576 = injectiveMoment H raw8576step0 := by
      have heq : raw8576step0 = (fun i j => raw8576 (permutation356 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8576 permutation356 permutation4
    _ = injectiveMoment H node2660 := by rfl

def raw8577 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![-1, -1, 2], ![1, 2, -3]]

def raw8577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, -2, 3]]

def raw8577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8577 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8577 = injectiveMoment H node2462 := by
  calc
    injectiveMoment H raw8577 = injectiveMoment H raw8577step0 := by
      have heq : raw8577step0 = -raw8577 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8577).symm
    injectiveMoment H raw8577step0 = injectiveMoment H raw8577step1 := by
      have heq : raw8577step1 = (fun i j => raw8577step0 (permutation373 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8577step0 permutation373 permutation3
    _ = injectiveMoment H node2462 := by rfl

def raw8578 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0]]

def raw8578step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8578 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8578 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw8578 = injectiveMoment H raw8578step0 := by
      have heq : raw8578step0 = (fun i j => raw8578 (permutation21 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8578 permutation21 permutation4
    _ = injectiveMoment H node271 := by rfl

def raw8579 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![-2, 2, 0], ![2, 1, -3]]

def raw8579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0], ![-2, -1, 3]]

def raw8579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical8579 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8579 = injectiveMoment H node1881 := by
  calc
    injectiveMoment H raw8579 = injectiveMoment H raw8579step0 := by
      have heq : raw8579step0 = -raw8579 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8579).symm
    injectiveMoment H raw8579step0 = injectiveMoment H raw8579step1 := by
      have heq : raw8579step1 = (fun i j => raw8579step0 (permutation373 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8579step0 permutation373 permutation3
    _ = injectiveMoment H node1881 := by rfl

def raw8580 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]

def raw8580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8580 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8580 = injectiveMoment H node1543 := by
  calc
    injectiveMoment H raw8580 = injectiveMoment H raw8580step0 := by
      have heq : raw8580step0 = (fun i j => raw8580 (permutation308 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8580 permutation308 permutation4
    _ = injectiveMoment H node1543 := by rfl

def raw8581 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-1, 3, -2], ![2, 1, -3]]

def raw8581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -3, 2], ![-2, -1, 3]]

def raw8581step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

theorem canonical8581 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8581 = injectiveMoment H node1889 := by
  calc
    injectiveMoment H raw8581 = injectiveMoment H raw8581step0 := by
      have heq : raw8581step0 = -raw8581 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8581).symm
    injectiveMoment H raw8581step0 = injectiveMoment H raw8581step1 := by
      have heq : raw8581step1 = (fun i j => raw8581step0 (permutation309 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8581step0 permutation309 permutation3
    _ = injectiveMoment H node1889 := by rfl

def raw8582 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 4, -3], ![1, -1, 0]]

def raw8582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8582 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8582 = injectiveMoment H node748 := by
  calc
    injectiveMoment H raw8582 = injectiveMoment H raw8582step0 := by
      have heq : raw8582step0 = (fun i j => raw8582 (permutation104 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8582 permutation104 permutation4
    _ = injectiveMoment H node748 := by rfl

def raw8583 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 3, -1], ![2, 1, -3]]

def raw8583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]

theorem canonical8583 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8583 = injectiveMoment H node1888 := by
  calc
    injectiveMoment H raw8583 = injectiveMoment H raw8583step0 := by
      have heq : raw8583step0 = (fun i j => raw8583 (permutation258 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8583 permutation258 permutation4
    _ = injectiveMoment H node1888 := by rfl

def raw8584 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![1, 1, -2]]

def raw8584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

theorem canonical8584 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8584 = injectiveMoment H node2480 := by
  calc
    injectiveMoment H raw8584 = injectiveMoment H raw8584step0 := by
      have heq : raw8584step0 = (fun i j => raw8584 (permutation258 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8584 permutation258 permutation4
    _ = injectiveMoment H node2480 := by rfl

def raw8585 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 4, -3]]

def raw8585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical8585 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8585 = injectiveMoment H node2384 := by
  calc
    injectiveMoment H raw8585 = injectiveMoment H raw8585step0 := by
      have heq : raw8585step0 = (fun i j => raw8585 (permutation308 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8585 permutation308 permutation4
    _ = injectiveMoment H node2384 := by rfl

def raw8586 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![-2, 2, 0], ![2, 1, -3]]

def raw8586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]

def raw8586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![-2, -1, 3]]

def raw8586step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical8586 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8586 = injectiveMoment H node566 := by
  calc
    injectiveMoment H raw8586 = injectiveMoment H raw8586step0 := by
      have heq : raw8586step0 = -raw8586 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8586).symm
    injectiveMoment H raw8586step0 = injectiveMoment H raw8586step1 := by
      have hz : ∀ j, raw8586step0 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw8586step1 = (fun i j => raw8586step0 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8586step0 permutation241 hz
    injectiveMoment H raw8586step1 = injectiveMoment H raw8586step2 := by
      have heq : raw8586step2 = (fun i j => raw8586step1 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8586step1 permutation128 permutation3
    _ = injectiveMoment H node566 := by rfl

def raw8587 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2]]

def raw8587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 3, -2]]

def raw8587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical8587 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8587 = injectiveMoment H node884 := by
  calc
    injectiveMoment H raw8587 = injectiveMoment H raw8587step0 := by
      have hz : ∀ j, raw8587 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw8587step0 = (fun i j => raw8587 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8587 permutation241 hz
    injectiveMoment H raw8587step0 = injectiveMoment H raw8587step1 := by
      have heq : raw8587step1 = (fun i j => raw8587step0 (permutation128 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8587step0 permutation128 permutation4
    _ = injectiveMoment H node884 := by rfl

def raw8588 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![-2, 4, -2]]

def raw8588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![-2, 4, -2]]

def raw8588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical8588 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8588 = injectiveMoment H node437 := by
  calc
    injectiveMoment H raw8588 = injectiveMoment H raw8588step0 := by
      have hz : ∀ j, raw8588 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw8588step0 = (fun i j => raw8588 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8588 permutation241 hz
    injectiveMoment H raw8588step0 = injectiveMoment H raw8588step1 := by
      have heq : raw8588step1 = (fun i j => raw8588step0 (permutation128 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8588step0 permutation128 permutation4
    _ = injectiveMoment H node437 := by rfl

def raw8589 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![2, 1, -3]]

def raw8589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![-2, -1, 3]]

def raw8589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical8589 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8589 = injectiveMoment H node1880 := by
  calc
    injectiveMoment H raw8589 = injectiveMoment H raw8589step0 := by
      have heq : raw8589step0 = -raw8589 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8589).symm
    injectiveMoment H raw8589step0 = injectiveMoment H raw8589step1 := by
      have heq : raw8589step1 = (fun i j => raw8589step0 (permutation373 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8589step0 permutation373 permutation3
    _ = injectiveMoment H node1880 := by rfl

def raw8590 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![2, 0, -2]]

def raw8590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical8590 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8590 = injectiveMoment H node2135 := by
  calc
    injectiveMoment H raw8590 = injectiveMoment H raw8590step0 := by
      have heq : raw8590step0 = (fun i j => raw8590 (permutation288 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8590 permutation288 permutation4
    _ = injectiveMoment H node2135 := by rfl

def raw8591 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def raw8591step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical8591 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8591 = injectiveMoment H node1323 := by
  calc
    injectiveMoment H raw8591 = injectiveMoment H raw8591step0 := by
      have hz : ∀ i, raw8591 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8591step0 = (fun i j => raw8591 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8591 permutation3 hz
    _ = injectiveMoment H node1323 := by rfl

def raw8592 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![0, -1, 1]]

def raw8592step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![4, -4], ![-1, 1]]

def raw8592step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical8592 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8592 = injectiveMoment H node69 := by
  calc
    injectiveMoment H raw8592 = injectiveMoment H raw8592step0 := by
      have hz : ∀ i, raw8592 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8592step0 = (fun i j => raw8592 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8592 permutation3 hz
    injectiveMoment H raw8592step0 = injectiveMoment H raw8592step1 := by
      have heq : raw8592step1 = (fun i j => raw8592step0 (permutation104 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8592step0 permutation104 permutation2
    _ = injectiveMoment H node69 := by rfl

def raw8593 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-3, 3, 0], ![2, 1, -3]]

def raw8593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]

theorem canonical8593 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8593 = injectiveMoment H node1411 := by
  calc
    injectiveMoment H raw8593 = injectiveMoment H raw8593step0 := by
      have heq : raw8593step0 = (fun i j => raw8593 (permutation258 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8593 permutation258 permutation4
    _ = injectiveMoment H node1411 := by rfl

def raw8594 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-2, 1, 1], ![1, 3, -4]]

def raw8594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical8594 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8594 = injectiveMoment H node2302 := by
  calc
    injectiveMoment H raw8594 = injectiveMoment H raw8594step0 := by
      have heq : raw8594step0 = (fun i j => raw8594 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8594 permutation258 permutation3
    _ = injectiveMoment H node2302 := by rfl

def raw8595 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-2, 3, -1], ![1, 1, -2]]

def raw8595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

theorem canonical8595 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8595 = injectiveMoment H node1890 := by
  calc
    injectiveMoment H raw8595 = injectiveMoment H raw8595step0 := by
      have heq : raw8595step0 = (fun i j => raw8595 (permutation259 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8595 permutation259 permutation4
    _ = injectiveMoment H node1890 := by rfl

def raw8596 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 4, -3]]

def raw8596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 4, -3]]

def raw8596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8596 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8596 = injectiveMoment H node748 := by
  calc
    injectiveMoment H raw8596 = injectiveMoment H raw8596step0 := by
      have hz : ∀ j, raw8596 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw8596step0 = (fun i j => raw8596 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8596 permutation258 hz
    injectiveMoment H raw8596step0 = injectiveMoment H raw8596step1 := by
      have heq : raw8596step1 = (fun i j => raw8596step0 (permutation128 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8596step0 permutation128 permutation4
    _ = injectiveMoment H node748 := by rfl

def raw8597 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 4, -2]]

def raw8597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8597 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8597 = injectiveMoment H node1542 := by
  calc
    injectiveMoment H raw8597 = injectiveMoment H raw8597step0 := by
      have heq : raw8597step0 = (fun i j => raw8597 (permutation309 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8597 permutation309 permutation4
    _ = injectiveMoment H node1542 := by rfl

def raw8598 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, -1, 2], ![0, 4, -4]]

def raw8598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

theorem canonical8598 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8598 = injectiveMoment H node2673 := by
  calc
    injectiveMoment H raw8598 = injectiveMoment H raw8598step0 := by
      have heq : raw8598step0 = (fun i j => raw8598 (permutation259 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8598 permutation259 permutation3
    _ = injectiveMoment H node2673 := by rfl

def raw8599 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![-1, 3, -2]]

def raw8599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 3, -2]]

def raw8599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical8599 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8599 = injectiveMoment H node884 := by
  calc
    injectiveMoment H raw8599 = injectiveMoment H raw8599step0 := by
      have hz : ∀ j, raw8599 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw8599step0 = (fun i j => raw8599 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8599 permutation258 hz
    injectiveMoment H raw8599step0 = injectiveMoment H raw8599step1 := by
      have heq : raw8599step1 = (fun i j => raw8599step0 (permutation128 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8599step0 permutation128 permutation4
    _ = injectiveMoment H node884 := by rfl

def raw8600 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![-2, 4, -2]]

def raw8600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8600 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8600 = injectiveMoment H node1542 := by
  calc
    injectiveMoment H raw8600 = injectiveMoment H raw8600step0 := by
      have heq : raw8600step0 = (fun i j => raw8600 (permutation308 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8600 permutation308 permutation4
    _ = injectiveMoment H node1542 := by rfl

def raw8601 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1]]

def raw8601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8601 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8601 = injectiveMoment H node1891 := by
  calc
    injectiveMoment H raw8601 = injectiveMoment H raw8601step0 := by
      have heq : raw8601step0 = (fun i j => raw8601 (permutation308 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8601 permutation308 permutation4
    _ = injectiveMoment H node1891 := by rfl

def raw8602 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![-3, 4, -1]]

def raw8602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

theorem canonical8602 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8602 = injectiveMoment H node1387 := by
  calc
    injectiveMoment H raw8602 = injectiveMoment H raw8602step0 := by
      have heq : raw8602step0 = (fun i j => raw8602 (permutation308 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8602 permutation308 permutation4
    _ = injectiveMoment H node1387 := by rfl

def raw8603 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def raw8603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def raw8603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical8603 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8603 = injectiveMoment H node1287 := by
  calc
    injectiveMoment H raw8603 = injectiveMoment H raw8603step0 := by
      have hz : ∀ j, raw8603 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8603step0 = (fun i j => raw8603 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8603 permutation221 hz
    injectiveMoment H raw8603step0 = injectiveMoment H raw8603step1 := by
      have heq : raw8603step1 = (fun i j => raw8603step0 (permutation38 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8603step0 permutation38 permutation5
    _ = injectiveMoment H node1287 := by rfl

def raw8604 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-2, 0, 2], ![2, 1, -3]]

def raw8604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![-2, -1, 3]]

def raw8604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![-2, -1, 3]]

def raw8604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical8604 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8604 = injectiveMoment H node555 := by
  calc
    injectiveMoment H raw8604 = injectiveMoment H raw8604step0 := by
      have heq : raw8604step0 = -raw8604 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8604).symm
    injectiveMoment H raw8604step0 = injectiveMoment H raw8604step1 := by
      have hz : ∀ j, raw8604step0 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8604step1 = (fun i j => raw8604step0 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8604step0 permutation221 hz
    injectiveMoment H raw8604step1 = injectiveMoment H raw8604step2 := by
      have heq : raw8604step2 = (fun i j => raw8604step1 (permutation139 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8604step1 permutation139 permutation3
    _ = injectiveMoment H node555 := by rfl

def raw8605 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-2, 1, 1], ![2, 0, -2]]

def raw8605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![-2, 0, 2]]

def raw8605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![-2, 0, 2]]

def raw8605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical8605 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8605 = injectiveMoment H node655 := by
  calc
    injectiveMoment H raw8605 = injectiveMoment H raw8605step0 := by
      have heq : raw8605step0 = -raw8605 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8605).symm
    injectiveMoment H raw8605step0 = injectiveMoment H raw8605step1 := by
      have hz : ∀ j, raw8605step0 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8605step1 = (fun i j => raw8605step0 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8605step0 permutation221 hz
    injectiveMoment H raw8605step1 = injectiveMoment H raw8605step2 := by
      have heq : raw8605step2 = (fun i j => raw8605step1 (permutation139 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8605step1 permutation139 permutation3
    _ = injectiveMoment H node655 := by rfl

def raw8606 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1]]

def raw8606step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1]]

def raw8606step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical8606 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8606 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw8606 = injectiveMoment H raw8606step0 := by
      have hz : ∀ j, raw8606 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw8606step0 = (fun i j => raw8606 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8606 permutation80 hz
    injectiveMoment H raw8606step0 = injectiveMoment H raw8606step1 := by
      have hz : ∀ i, raw8606step0 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8606step1 = (fun i j => raw8606step0 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8606step0 permutation3 hz
    _ = injectiveMoment H node65 := by rfl

def raw8607 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![1, 3, -4]]

def raw8607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-2, 0, 2], ![1, 3, -4]]

def raw8607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical8607 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8607 = injectiveMoment H node653 := by
  calc
    injectiveMoment H raw8607 = injectiveMoment H raw8607step0 := by
      have hz : ∀ j, raw8607 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8607step0 = (fun i j => raw8607 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8607 permutation221 hz
    injectiveMoment H raw8607step0 = injectiveMoment H raw8607step1 := by
      have heq : raw8607step1 = (fun i j => raw8607step0 (permutation104 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8607step0 permutation104 permutation3
    _ = injectiveMoment H node653 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
