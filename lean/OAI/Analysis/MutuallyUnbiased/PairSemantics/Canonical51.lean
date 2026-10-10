import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1632 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, 1, -2]]

theorem canonical1632 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1632 = injectiveMoment H node459 := by
  rfl

def raw1633 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical1633 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1633 = injectiveMoment H node1611 := by
  rfl

def raw1634 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw1634step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical1634 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1634 = injectiveMoment H node450 := by
  calc
    injectiveMoment H raw1634 = injectiveMoment H raw1634step0 := by
      have heq : raw1634step0 = (fun i j => raw1634 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1634 permutation11 permutation11
    _ = injectiveMoment H node450 := by rfl

def raw1635 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical1635 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1635 = injectiveMoment H node1612 := by
  rfl

def raw1636 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical1636 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1636 = injectiveMoment H node1613 := by
  rfl

def raw1637 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, -1, -1, 0]]

def raw1637step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![-1, 2, 0, -1], ![4, -2, -2, 0]]

def raw1637step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical1637 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1637 = injectiveMoment H node396 := by
  calc
    injectiveMoment H raw1637 = injectiveMoment H raw1637step0 := by
      have heq : raw1637step0 = raw1637.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1637).symm
    injectiveMoment H raw1637step0 = injectiveMoment H raw1637step1 := by
      have heq : raw1637step1 = (fun i j => raw1637step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1637step0 permutation27 permutation18
    _ = injectiveMoment H node396 := by rfl

def raw1638 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

theorem canonical1638 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1638 = injectiveMoment H node460 := by
  rfl

def raw1639 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def raw1639step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![-1, 2, 0, -1], ![4, -2, 0, -2]]

def raw1639step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 0, 1, -2], ![1, -2, 0, 1], ![-4, 2, 0, 2]]

def raw1639step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical1639 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1639 = injectiveMoment H node1234 := by
  calc
    injectiveMoment H raw1639 = injectiveMoment H raw1639step0 := by
      have heq : raw1639step0 = raw1639.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1639).symm
    injectiveMoment H raw1639step0 = injectiveMoment H raw1639step1 := by
      have heq : raw1639step1 = -raw1639step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1639step0).symm
    injectiveMoment H raw1639step1 = injectiveMoment H raw1639step2 := by
      have heq : raw1639step2 = (fun i j => raw1639step1 (permutation12 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1639step1 permutation12 permutation24
    _ = injectiveMoment H node1234 := by rfl

def raw1640 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 2, -2, -1]]

def raw1640step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![-1, 2, 1, -2], ![4, -2, -1, -1]]

def raw1640step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 1, -2, -1]]

theorem canonical1640 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1640 = injectiveMoment H node447 := by
  calc
    injectiveMoment H raw1640 = injectiveMoment H raw1640step0 := by
      have heq : raw1640step0 = raw1640.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1640).symm
    injectiveMoment H raw1640step0 = injectiveMoment H raw1640step1 := by
      have heq : raw1640step1 = (fun i j => raw1640step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1640step0 permutation29 permutation18
    _ = injectiveMoment H node447 := by rfl

def raw1641 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1641step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical1641 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1641 = injectiveMoment H node771 := by
  calc
    injectiveMoment H raw1641 = injectiveMoment H raw1641step0 := by
      have heq : raw1641step0 = (fun i j => raw1641 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1641 permutation9 permutation15
    _ = injectiveMoment H node771 := by rfl

def raw1642 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1642step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![-1, 2, 0, -1], ![4, -2, -1, -1]]

def raw1642step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical1642 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1642 = injectiveMoment H node769 := by
  calc
    injectiveMoment H raw1642 = injectiveMoment H raw1642step0 := by
      have heq : raw1642step0 = raw1642.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1642).symm
    injectiveMoment H raw1642step0 = injectiveMoment H raw1642step1 := by
      have heq : raw1642step1 = (fun i j => raw1642step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1642step0 permutation30 permutation24
    _ = injectiveMoment H node769 := by rfl

def raw1643 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw1643step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical1643 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1643 = injectiveMoment H node772 := by
  calc
    injectiveMoment H raw1643 = injectiveMoment H raw1643step0 := by
      have heq : raw1643step0 = (fun i j => raw1643 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1643 permutation9 permutation15
    _ = injectiveMoment H node772 := by rfl

def raw1644 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw1644step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical1644 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1644 = injectiveMoment H node772 := by
  calc
    injectiveMoment H raw1644 = injectiveMoment H raw1644step0 := by
      have heq : raw1644step0 = (fun i j => raw1644 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1644 permutation10 permutation15
    _ = injectiveMoment H node772 := by rfl

def raw1645 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, 1, 0, -2], ![1, 0, -1, 0]]

def raw1645step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical1645 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1645 = injectiveMoment H node771 := by
  calc
    injectiveMoment H raw1645 = injectiveMoment H raw1645step0 := by
      have heq : raw1645step0 = (fun i j => raw1645 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1645 permutation10 permutation15
    _ = injectiveMoment H node771 := by rfl

def raw1646 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, 2, -2, -1], ![1, -1, 1, -1]]

def raw1646step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 2, -1], ![-1, 2, -2, 1], ![4, -2, -1, -1]]

def raw1646step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 1, -2, -1]]

theorem canonical1646 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1646 = injectiveMoment H node447 := by
  calc
    injectiveMoment H raw1646 = injectiveMoment H raw1646step0 := by
      have heq : raw1646step0 = raw1646.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1646).symm
    injectiveMoment H raw1646step0 = injectiveMoment H raw1646step1 := by
      have heq : raw1646step1 = (fun i j => raw1646step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1646step0 permutation29 permutation20
    _ = injectiveMoment H node447 := by rfl

def raw1647 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, 2, 0, -3], ![1, -1, -1, 1]]

def raw1647step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

theorem canonical1647 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1647 = injectiveMoment H node460 := by
  calc
    injectiveMoment H raw1647 = injectiveMoment H raw1647step0 := by
      have heq : raw1647step0 = (fun i j => raw1647 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1647 permutation10 permutation9
    _ = injectiveMoment H node460 := by rfl

def raw1648 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, -1, 0, -1]]

theorem canonical1648 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1648 = injectiveMoment H node461 := by
  rfl

def raw1649 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw1649step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![-1, 3, 0, -2], ![4, -3, 0, -1]]

def raw1649step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 0, 1, -2], ![1, -3, 0, 2], ![-4, 3, 0, 1]]

def raw1649step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 3, -4], ![0, 2, -3, 1], ![1, -2, 0, 1]]

theorem canonical1649 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1649 = injectiveMoment H node1086 := by
  calc
    injectiveMoment H raw1649 = injectiveMoment H raw1649step0 := by
      have heq : raw1649step0 = raw1649.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1649).symm
    injectiveMoment H raw1649step0 = injectiveMoment H raw1649step1 := by
      have heq : raw1649step1 = -raw1649step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1649step0).symm
    injectiveMoment H raw1649step1 = injectiveMoment H raw1649step2 := by
      have heq : raw1649step2 = (fun i j => raw1649step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1649step1 permutation14 permutation26
    _ = injectiveMoment H node1086 := by rfl

def raw1650 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 0, 1, -1], ![2, 0, 1, -3]]

def raw1650step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 0, 0], ![-1, -1, 1, 1], ![4, 0, -1, -3]]

def raw1650step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

theorem canonical1650 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1650 = injectiveMoment H node1177 := by
  calc
    injectiveMoment H raw1650 = injectiveMoment H raw1650step0 := by
      have heq : raw1650step0 = raw1650.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1650).symm
    injectiveMoment H raw1650step0 = injectiveMoment H raw1650step1 := by
      have heq : raw1650step1 = (fun i j => raw1650step0 (permutation27 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1650step0 permutation27 permutation24
    _ = injectiveMoment H node1177 := by rfl

def raw1651 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 0, 2, -2], ![2, 0, 0, -2]]

def raw1651step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical1651 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1651 = injectiveMoment H node775 := by
  calc
    injectiveMoment H raw1651 = injectiveMoment H raw1651step0 := by
      have heq : raw1651step0 = (fun i j => raw1651 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1651 permutation12 permutation15
    _ = injectiveMoment H node775 := by rfl

def raw1652 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical1652 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1652 = injectiveMoment H node1614 := by
  rfl

def raw1653 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

theorem canonical1653 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1653 = injectiveMoment H node1615 := by
  rfl

def raw1654 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 3, -4]]

def raw1654step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![-1, -1, -1, 3], ![4, 0, 0, -4]]

def raw1654step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -2, 2], ![0, 0, 4, -4], ![1, 1, -1, -1]]

theorem canonical1654 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1654 = injectiveMoment H node957 := by
  calc
    injectiveMoment H raw1654 = injectiveMoment H raw1654step0 := by
      have heq : raw1654step0 = raw1654.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1654).symm
    injectiveMoment H raw1654step0 = injectiveMoment H raw1654step1 := by
      have heq : raw1654step1 = (fun i j => raw1654step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1654step0 permutation22 permutation17
    _ = injectiveMoment H node957 := by rfl

def raw1655 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw1655step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

theorem canonical1655 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1655 = injectiveMoment H node1551 := by
  calc
    injectiveMoment H raw1655 = injectiveMoment H raw1655step0 := by
      have heq : raw1655step0 = (fun i j => raw1655 (permutation33 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1655 permutation33 permutation11
    _ = injectiveMoment H node1551 := by rfl

def raw1656 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw1656step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical1656 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1656 = injectiveMoment H node1553 := by
  calc
    injectiveMoment H raw1656 = injectiveMoment H raw1656step0 := by
      have heq : raw1656step0 = (fun i j => raw1656 (permutation33 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1656 permutation33 permutation11
    _ = injectiveMoment H node1553 := by rfl

def raw1657 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw1657step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

theorem canonical1657 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1657 = injectiveMoment H node1552 := by
  calc
    injectiveMoment H raw1657 = injectiveMoment H raw1657step0 := by
      have heq : raw1657step0 = (fun i j => raw1657 (permutation34 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1657 permutation34 permutation11
    _ = injectiveMoment H node1552 := by rfl

def raw1658 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 2, -3]]

def raw1658step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![-1, -1, 0, 2], ![4, 0, -1, -3]]

def raw1658step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![1, 1, 0, -2], ![-4, 0, 1, 3]]

def raw1658step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -2, 1], ![1, 0, 3, -4]]

theorem canonical1658 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1658 = injectiveMoment H node1108 := by
  calc
    injectiveMoment H raw1658 = injectiveMoment H raw1658step0 := by
      have heq : raw1658step0 = raw1658.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1658).symm
    injectiveMoment H raw1658step0 = injectiveMoment H raw1658step1 := by
      have heq : raw1658step1 = -raw1658step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1658step0).symm
    injectiveMoment H raw1658step1 = injectiveMoment H raw1658step2 := by
      have heq : raw1658step2 = (fun i j => raw1658step1 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1658step1 permutation15 permutation24
    _ = injectiveMoment H node1108 := by rfl

def raw1659 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw1659step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![-1, -1, 1, 1], ![4, 0, -2, -2]]

def raw1659step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![1, 1, -1, -1], ![-4, 0, 2, 2]]

def raw1659step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem canonical1659 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1659 = injectiveMoment H node1113 := by
  calc
    injectiveMoment H raw1659 = injectiveMoment H raw1659step0 := by
      have heq : raw1659step0 = raw1659.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1659).symm
    injectiveMoment H raw1659step0 = injectiveMoment H raw1659step1 := by
      have heq : raw1659step1 = -raw1659step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1659step0).symm
    injectiveMoment H raw1659step1 = injectiveMoment H raw1659step2 := by
      have heq : raw1659step2 = (fun i j => raw1659step1 (permutation16 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1659step1 permutation16 permutation18
    _ = injectiveMoment H node1113 := by rfl

def raw1660 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw1660step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical1660 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1660 = injectiveMoment H node1563 := by
  calc
    injectiveMoment H raw1660 = injectiveMoment H raw1660step0 := by
      have heq : raw1660step0 = (fun i j => raw1660 (permutation33 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1660 permutation33 permutation11
    _ = injectiveMoment H node1563 := by rfl

def raw1661 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical1661 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1661 = injectiveMoment H node1616 := by
  rfl

def raw1662 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -1, 0, -1]]

def raw1662step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![-1, -1, 2, 0], ![4, 0, -3, -1]]

def raw1662step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical1662 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1662 = injectiveMoment H node1306 := by
  calc
    injectiveMoment H raw1662 = injectiveMoment H raw1662step0 := by
      have heq : raw1662step0 = raw1662.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1662).symm
    injectiveMoment H raw1662step0 = injectiveMoment H raw1662step1 := by
      have heq : raw1662step1 = (fun i j => raw1662step0 (permutation25 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1662step0 permutation25 permutation20
    _ = injectiveMoment H node1306 := by rfl

def raw1663 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical1663 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1663 = injectiveMoment H node1617 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
