import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1664 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw1664step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![-1, -1, 0, 2], ![4, 0, 0, -4]]

def raw1664step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, -1, -1, 1]]

theorem canonical1664 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1664 = injectiveMoment H node1272 := by
  calc
    injectiveMoment H raw1664 = injectiveMoment H raw1664step0 := by
      have heq : raw1664step0 = raw1664.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1664).symm
    injectiveMoment H raw1664step0 = injectiveMoment H raw1664step1 := by
      have heq : raw1664step1 = (fun i j => raw1664step0 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1664step0 permutation25 permutation17
    _ = injectiveMoment H node1272 := by rfl

def raw1665 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def raw1665step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![-1, -1, 1, 1], ![4, 0, -1, -3]]

def raw1665step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1], ![-4, 0, 1, 3]]

def raw1665step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical1665 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1665 = injectiveMoment H node1341 := by
  calc
    injectiveMoment H raw1665 = injectiveMoment H raw1665step0 := by
      have heq : raw1665step0 = raw1665.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1665).symm
    injectiveMoment H raw1665step0 = injectiveMoment H raw1665step1 := by
      have heq : raw1665step1 = -raw1665step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1665step0).symm
    injectiveMoment H raw1665step1 = injectiveMoment H raw1665step2 := by
      have heq : raw1665step2 = (fun i j => raw1665step1 (permutation16 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1665step1 permutation16 permutation18
    _ = injectiveMoment H node1341 := by rfl

def raw1666 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def raw1666step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![-1, -1, 2, 0], ![4, 0, -2, -2]]

def raw1666step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![1, 1, -2, 0], ![-4, 0, 2, 2]]

def raw1666step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical1666 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1666 = injectiveMoment H node1100 := by
  calc
    injectiveMoment H raw1666 = injectiveMoment H raw1666step0 := by
      have heq : raw1666step0 = raw1666.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1666).symm
    injectiveMoment H raw1666step0 = injectiveMoment H raw1666step1 := by
      have heq : raw1666step1 = -raw1666step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1666step0).symm
    injectiveMoment H raw1666step1 = injectiveMoment H raw1666step2 := by
      have heq : raw1666step2 = (fun i j => raw1666step1 (permutation16 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1666step1 permutation16 permutation20
    _ = injectiveMoment H node1100 := by rfl

def raw1667 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw1667step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-1, -1, -1, 3], ![4, 0, 0, -4]]

def raw1667step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, 0, -1, 0]]

theorem canonical1667 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1667 = injectiveMoment H node981 := by
  calc
    injectiveMoment H raw1667 = injectiveMoment H raw1667step0 := by
      have heq : raw1667step0 = raw1667.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1667).symm
    injectiveMoment H raw1667step0 = injectiveMoment H raw1667step1 := by
      have heq : raw1667step1 = (fun i j => raw1667step0 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1667step0 permutation25 permutation17
    _ = injectiveMoment H node981 := by rfl

def raw1668 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def raw1668step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-1, -1, 0, 2], ![4, 0, -1, -3]]

def raw1668step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical1668 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1668 = injectiveMoment H node1170 := by
  calc
    injectiveMoment H raw1668 = injectiveMoment H raw1668step0 := by
      have heq : raw1668step0 = raw1668.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1668).symm
    injectiveMoment H raw1668step0 = injectiveMoment H raw1668step1 := by
      have heq : raw1668step1 = (fun i j => raw1668step0 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1668step0 permutation32 permutation24
    _ = injectiveMoment H node1170 := by rfl

def raw1669 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def raw1669step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical1669 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1669 = injectiveMoment H node787 := by
  calc
    injectiveMoment H raw1669 = injectiveMoment H raw1669step0 := by
      have heq : raw1669step0 = (fun i j => raw1669 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1669 permutation12 permutation15
    _ = injectiveMoment H node787 := by rfl

def raw1670 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1670step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 1, 0, 0, 0], ![-1, 0, 0, -1, 2], ![4, -1, 0, 0, -3]]

def raw1670step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-1, 0, -1, 2], ![4, -1, 0, -3]]

def raw1670step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical1670 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1670 = injectiveMoment H node1171 := by
  calc
    injectiveMoment H raw1670 = injectiveMoment H raw1670step0 := by
      have heq : raw1670step0 = raw1670.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1670).symm
    injectiveMoment H raw1670step0 = injectiveMoment H raw1670step1 := by
      have hz : ∀ i, raw1670step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw1670step1 = (fun i j => raw1670step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1670step0 permutation80 hz
    injectiveMoment H raw1670step1 = injectiveMoment H raw1670step2 := by
      have heq : raw1670step2 = (fun i j => raw1670step1 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1670step1 permutation31 permutation18
    _ = injectiveMoment H node1171 := by rfl

def raw1671 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1671step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical1671 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1671 = injectiveMoment H node2400 := by
  calc
    injectiveMoment H raw1671 = injectiveMoment H raw1671step0 := by
      have heq : raw1671step0 = (fun i j => raw1671 (permutation42 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1671 permutation42 permutation15
    _ = injectiveMoment H node2400 := by rfl

def raw1672 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1672step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical1672 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1672 = injectiveMoment H node2402 := by
  calc
    injectiveMoment H raw1672 = injectiveMoment H raw1672step0 := by
      have heq : raw1672step0 = (fun i j => raw1672 (permutation42 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1672 permutation42 permutation15
    _ = injectiveMoment H node2402 := by rfl

def raw1673 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 0, 2, -2], ![2, 0, -1, -1]]

def raw1673step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical1673 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1673 = injectiveMoment H node774 := by
  calc
    injectiveMoment H raw1673 = injectiveMoment H raw1673step0 := by
      have heq : raw1673step0 = (fun i j => raw1673 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1673 permutation12 permutation15
    _ = injectiveMoment H node774 := by rfl

def raw1674 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw1674step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

theorem canonical1674 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1674 = injectiveMoment H node1551 := by
  calc
    injectiveMoment H raw1674 = injectiveMoment H raw1674step0 := by
      have heq : raw1674step0 = (fun i j => raw1674 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1674 permutation39 permutation11
    _ = injectiveMoment H node1551 := by rfl

def raw1675 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def raw1675step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![-1, 0, -1, 2], ![4, -1, 0, -3]]

def raw1675step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2], ![-4, 1, 0, 3]]

def raw1675step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -2, 1], ![1, 0, 3, -4]]

theorem canonical1675 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1675 = injectiveMoment H node1108 := by
  calc
    injectiveMoment H raw1675 = injectiveMoment H raw1675step0 := by
      have heq : raw1675step0 = raw1675.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1675).symm
    injectiveMoment H raw1675step0 = injectiveMoment H raw1675step1 := by
      have heq : raw1675step1 = -raw1675step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1675step0).symm
    injectiveMoment H raw1675step1 = injectiveMoment H raw1675step2 := by
      have heq : raw1675step2 = (fun i j => raw1675step1 (permutation15 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1675step1 permutation15 permutation18
    _ = injectiveMoment H node1108 := by rfl

def raw1676 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw1676step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, 0, -3]]

theorem canonical1676 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1676 = injectiveMoment H node1584 := by
  calc
    injectiveMoment H raw1676 = injectiveMoment H raw1676step0 := by
      have heq : raw1676step0 = (fun i j => raw1676 (permutation33 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1676 permutation33 permutation11
    _ = injectiveMoment H node1584 := by rfl

def raw1677 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw1677step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical1677 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1677 = injectiveMoment H node2390 := by
  calc
    injectiveMoment H raw1677 = injectiveMoment H raw1677step0 := by
      have heq : raw1677step0 = (fun i j => raw1677 (permutation33 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1677 permutation33 permutation21
    _ = injectiveMoment H node2390 := by rfl

def raw1678 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw1678step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

theorem canonical1678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1678 = injectiveMoment H node1585 := by
  calc
    injectiveMoment H raw1678 = injectiveMoment H raw1678step0 := by
      have heq : raw1678step0 = (fun i j => raw1678 (permutation34 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1678 permutation34 permutation11
    _ = injectiveMoment H node1585 := by rfl

def raw1679 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 2, -2]]

def raw1679step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

theorem canonical1679 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1679 = injectiveMoment H node1585 := by
  calc
    injectiveMoment H raw1679 = injectiveMoment H raw1679step0 := by
      have heq : raw1679step0 = (fun i j => raw1679 (permutation33 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1679 permutation33 permutation11
    _ = injectiveMoment H node1585 := by rfl

def raw1680 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw1680step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical1680 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1680 = injectiveMoment H node2399 := by
  calc
    injectiveMoment H raw1680 = injectiveMoment H raw1680step0 := by
      have heq : raw1680step0 = (fun i j => raw1680 (permutation36 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1680 permutation36 permutation21
    _ = injectiveMoment H node2399 := by rfl

def raw1681 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw1681step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical1681 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1681 = injectiveMoment H node1595 := by
  calc
    injectiveMoment H raw1681 = injectiveMoment H raw1681step0 := by
      have heq : raw1681step0 = (fun i j => raw1681 (permutation34 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1681 permutation34 permutation11
    _ = injectiveMoment H node1595 := by rfl

def raw1682 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw1682step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical1682 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1682 = injectiveMoment H node1595 := by
  calc
    injectiveMoment H raw1682 = injectiveMoment H raw1682step0 := by
      have heq : raw1682step0 = (fun i j => raw1682 (permutation33 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1682 permutation33 permutation11
    _ = injectiveMoment H node1595 := by rfl

def raw1683 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw1683step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical1683 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1683 = injectiveMoment H node769 := by
  calc
    injectiveMoment H raw1683 = injectiveMoment H raw1683step0 := by
      have heq : raw1683step0 = (fun i j => raw1683 (permutation10 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1683 permutation10 permutation21
    _ = injectiveMoment H node769 := by rfl

def raw1684 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw1684step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical1684 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1684 = injectiveMoment H node1605 := by
  calc
    injectiveMoment H raw1684 = injectiveMoment H raw1684step0 := by
      have heq : raw1684step0 = (fun i j => raw1684 (permutation34 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1684 permutation34 permutation11
    _ = injectiveMoment H node1605 := by rfl

def raw1685 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![2, -1, -1, 0]]

def raw1685step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![-1, 0, 2, -1], ![4, -1, -3, 0]]

def raw1685step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical1685 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1685 = injectiveMoment H node1173 := by
  calc
    injectiveMoment H raw1685 = injectiveMoment H raw1685step0 := by
      have heq : raw1685step0 = raw1685.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1685).symm
    injectiveMoment H raw1685step0 = injectiveMoment H raw1685step1 := by
      have heq : raw1685step1 = (fun i j => raw1685step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1685step0 permutation31 permutation20
    _ = injectiveMoment H node1173 := by rfl

def raw1686 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw1686step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![-1, 0, -1, 2], ![4, -1, 1, -4]]

def raw1686step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -4, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical1686 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1686 = injectiveMoment H node1324 := by
  calc
    injectiveMoment H raw1686 = injectiveMoment H raw1686step0 := by
      have heq : raw1686step0 = raw1686.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1686).symm
    injectiveMoment H raw1686step0 = injectiveMoment H raw1686step1 := by
      have heq : raw1686step1 = (fun i j => raw1686step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1686step0 permutation31 permutation18
    _ = injectiveMoment H node1324 := by rfl

def raw1687 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw1687step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![-1, 0, 0, 1], ![4, -1, 0, -3]]

def raw1687step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical1687 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1687 = injectiveMoment H node1176 := by
  calc
    injectiveMoment H raw1687 = injectiveMoment H raw1687step0 := by
      have heq : raw1687step0 = raw1687.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1687).symm
    injectiveMoment H raw1687step0 = injectiveMoment H raw1687step1 := by
      have heq : raw1687step1 = (fun i j => raw1687step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1687step0 permutation31 permutation18
    _ = injectiveMoment H node1176 := by rfl

def raw1688 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw1688step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical1688 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1688 = injectiveMoment H node766 := by
  calc
    injectiveMoment H raw1688 = injectiveMoment H raw1688step0 := by
      have heq : raw1688step0 = (fun i j => raw1688 (permutation10 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1688 permutation10 permutation21
    _ = injectiveMoment H node766 := by rfl

def raw1689 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def raw1689step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![-1, 0, 2, -1], ![4, -1, -2, -1]]

def raw1689step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical1689 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1689 = injectiveMoment H node894 := by
  calc
    injectiveMoment H raw1689 = injectiveMoment H raw1689step0 := by
      have heq : raw1689step0 = raw1689.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1689).symm
    injectiveMoment H raw1689step0 = injectiveMoment H raw1689step1 := by
      have heq : raw1689step1 = (fun i j => raw1689step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1689step0 permutation31 permutation20
    _ = injectiveMoment H node894 := by rfl

def raw1690 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 1, -2, 0]]

def raw1690step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![-1, 0, 3, -2], ![4, -1, -3, 0]]

def raw1690step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![1, 0, -3, 2], ![-4, 1, 3, 0]]

def raw1690step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, -3, 1], ![1, 0, 3, -4]]

theorem canonical1690 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1690 = injectiveMoment H node1097 := by
  calc
    injectiveMoment H raw1690 = injectiveMoment H raw1690step0 := by
      have heq : raw1690step0 = raw1690.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1690).symm
    injectiveMoment H raw1690step0 = injectiveMoment H raw1690step1 := by
      have heq : raw1690step1 = -raw1690step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1690step0).symm
    injectiveMoment H raw1690step1 = injectiveMoment H raw1690step2 := by
      have heq : raw1690step2 = (fun i j => raw1690step1 (permutation15 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1690step1 permutation15 permutation20
    _ = injectiveMoment H node1097 := by rfl

def raw1691 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1691step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-1, 0, -1, 2], ![4, -1, 0, -3]]

def raw1691step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical1691 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1691 = injectiveMoment H node1171 := by
  calc
    injectiveMoment H raw1691 = injectiveMoment H raw1691step0 := by
      have heq : raw1691step0 = raw1691.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1691).symm
    injectiveMoment H raw1691step0 = injectiveMoment H raw1691step1 := by
      have heq : raw1691step1 = (fun i j => raw1691step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1691step0 permutation31 permutation18
    _ = injectiveMoment H node1171 := by rfl

def raw1692 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1692step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical1692 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1692 = injectiveMoment H node910 := by
  calc
    injectiveMoment H raw1692 = injectiveMoment H raw1692step0 := by
      have heq : raw1692step0 = (fun i j => raw1692 (permutation11 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1692 permutation11 permutation23
    _ = injectiveMoment H node910 := by rfl

def raw1693 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw1693step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical1693 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1693 = injectiveMoment H node910 := by
  calc
    injectiveMoment H raw1693 = injectiveMoment H raw1693step0 := by
      have heq : raw1693step0 = (fun i j => raw1693 (permutation13 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1693 permutation13 permutation23
    _ = injectiveMoment H node910 := by rfl

def raw1694 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 0, -1, 0]]

def raw1694step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![-1, 0, 2, -1], ![4, -1, -3, 0]]

def raw1694step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical1694 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1694 = injectiveMoment H node1171 := by
  calc
    injectiveMoment H raw1694 = injectiveMoment H raw1694step0 := by
      have heq : raw1694step0 = raw1694.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1694).symm
    injectiveMoment H raw1694step0 = injectiveMoment H raw1694step1 := by
      have heq : raw1694step1 = (fun i j => raw1694step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1694step0 permutation31 permutation20
    _ = injectiveMoment H node1171 := by rfl

def raw1695 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw1695step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![-1, 1, -1, 1], ![4, -2, 0, -2]]

def raw1695step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![1, -1, 1, -1], ![-4, 2, 0, 2]]

def raw1695step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem canonical1695 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1695 = injectiveMoment H node1113 := by
  calc
    injectiveMoment H raw1695 = injectiveMoment H raw1695step0 := by
      have heq : raw1695step0 = raw1695.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1695).symm
    injectiveMoment H raw1695step0 = injectiveMoment H raw1695step1 := by
      have heq : raw1695step1 = -raw1695step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1695step0).symm
    injectiveMoment H raw1695step1 = injectiveMoment H raw1695step2 := by
      have heq : raw1695step2 = (fun i j => raw1695step1 (permutation16 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1695step1 permutation16 permutation24
    _ = injectiveMoment H node1113 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
