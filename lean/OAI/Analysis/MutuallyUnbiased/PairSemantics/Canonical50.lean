import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1600 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem canonical1600 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1600 = injectiveMoment H node1602 := by
  rfl

def raw1601 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw1601step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical1601 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1601 = injectiveMoment H node2402 := by
  calc
    injectiveMoment H raw1601 = injectiveMoment H raw1601step0 := by
      have heq : raw1601step0 = (fun i j => raw1601 (permutation42 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1601 permutation42 permutation21
    _ = injectiveMoment H node2402 := by rfl

def raw1602 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical1602 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1602 = injectiveMoment H node1603 := by
  rfl

def raw1603 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw1603step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical1603 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1603 = injectiveMoment H node1603 := by
  calc
    injectiveMoment H raw1603 = injectiveMoment H raw1603step0 := by
      have heq : raw1603step0 = (fun i j => raw1603 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1603 permutation34 permutation9
    _ = injectiveMoment H node1603 := by rfl

def raw1604 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw1604step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical1604 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1604 = injectiveMoment H node774 := by
  calc
    injectiveMoment H raw1604 = injectiveMoment H raw1604step0 := by
      have heq : raw1604step0 = (fun i j => raw1604 (permutation12 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1604 permutation12 permutation21
    _ = injectiveMoment H node774 := by rfl

def raw1605 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical1605 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1605 = injectiveMoment H node1604 := by
  rfl

def raw1606 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical1606 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1606 = injectiveMoment H node1605 := by
  rfl

def raw1607 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw1607step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical1607 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1607 = injectiveMoment H node1605 := by
  calc
    injectiveMoment H raw1607 = injectiveMoment H raw1607step0 := by
      have heq : raw1607step0 = (fun i j => raw1607 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1607 permutation34 permutation9
    _ = injectiveMoment H node1605 := by rfl

def raw1608 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![2, -1, -1, 0]]

def raw1608step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![-1, 1, 1, -1], ![4, -1, -3, 0]]

def raw1608step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical1608 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1608 = injectiveMoment H node1173 := by
  calc
    injectiveMoment H raw1608 = injectiveMoment H raw1608step0 := by
      have heq : raw1608step0 = raw1608.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1608).symm
    injectiveMoment H raw1608step0 = injectiveMoment H raw1608step1 := by
      have heq : raw1608step1 = (fun i j => raw1608step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1608step0 permutation29 permutation20
    _ = injectiveMoment H node1173 := by rfl

def raw1609 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, 1, -4]]

def raw1609step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![-1, 1, -1, 1], ![4, -1, 1, -4]]

def raw1609step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -4, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical1609 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1609 = injectiveMoment H node1324 := by
  calc
    injectiveMoment H raw1609 = injectiveMoment H raw1609step0 := by
      have heq : raw1609step0 = raw1609.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1609).symm
    injectiveMoment H raw1609step0 = injectiveMoment H raw1609step1 := by
      have heq : raw1609step1 = (fun i j => raw1609step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1609step0 permutation29 permutation18
    _ = injectiveMoment H node1324 := by rfl

def raw1610 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw1610step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![-1, 1, 0, 0], ![4, -1, 0, -3]]

def raw1610step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical1610 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1610 = injectiveMoment H node1171 := by
  calc
    injectiveMoment H raw1610 = injectiveMoment H raw1610step0 := by
      have heq : raw1610step0 = raw1610.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1610).symm
    injectiveMoment H raw1610step0 = injectiveMoment H raw1610step1 := by
      have heq : raw1610step1 = (fun i j => raw1610step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1610step0 permutation29 permutation18
    _ = injectiveMoment H node1171 := by rfl

def raw1611 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, -1, -2]]

def raw1611step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![-1, 1, 1, -1], ![4, -1, -1, -2]]

def raw1611step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical1611 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1611 = injectiveMoment H node894 := by
  calc
    injectiveMoment H raw1611 = injectiveMoment H raw1611step0 := by
      have heq : raw1611step0 = raw1611.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1611).symm
    injectiveMoment H raw1611step0 = injectiveMoment H raw1611step1 := by
      have heq : raw1611step1 = (fun i j => raw1611step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1611step0 permutation29 permutation18
    _ = injectiveMoment H node894 := by rfl

def raw1612 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 2, -2, -1]]

def raw1612step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![-1, 1, 2, -2], ![4, -1, -2, -1]]

def raw1612step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 2, -2, -1]]

theorem canonical1612 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1612 = injectiveMoment H node756 := by
  calc
    injectiveMoment H raw1612 = injectiveMoment H raw1612step0 := by
      have heq : raw1612step0 = raw1612.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1612).symm
    injectiveMoment H raw1612step0 = injectiveMoment H raw1612step1 := by
      have heq : raw1612step1 = (fun i j => raw1612step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1612step0 permutation29 permutation18
    _ = injectiveMoment H node756 := by rfl

def raw1613 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw1613step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![-1, 1, -1, 1], ![4, -1, 0, -3]]

def raw1613step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical1613 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1613 = injectiveMoment H node1176 := by
  calc
    injectiveMoment H raw1613 = injectiveMoment H raw1613step0 := by
      have heq : raw1613step0 = raw1613.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1613).symm
    injectiveMoment H raw1613step0 = injectiveMoment H raw1613step1 := by
      have heq : raw1613step1 = (fun i j => raw1613step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1613step0 permutation29 permutation18
    _ = injectiveMoment H node1176 := by rfl

def raw1614 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1614step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical1614 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1614 = injectiveMoment H node910 := by
  calc
    injectiveMoment H raw1614 = injectiveMoment H raw1614step0 := by
      have heq : raw1614step0 = (fun i j => raw1614 (permutation11 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1614 permutation11 permutation17
    _ = injectiveMoment H node910 := by rfl

def raw1615 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw1615step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical1615 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1615 = injectiveMoment H node766 := by
  calc
    injectiveMoment H raw1615 = injectiveMoment H raw1615step0 := by
      have heq : raw1615step0 = (fun i j => raw1615 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1615 permutation9 permutation15
    _ = injectiveMoment H node766 := by rfl

def raw1616 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 0, 1, -2]]

def raw1616step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical1616 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1616 = injectiveMoment H node766 := by
  calc
    injectiveMoment H raw1616 = injectiveMoment H raw1616step0 := by
      have heq : raw1616step0 = (fun i j => raw1616 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1616 permutation10 permutation15
    _ = injectiveMoment H node766 := by rfl

def raw1617 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def raw1617step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, 0, -1]]

theorem canonical1617 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1617 = injectiveMoment H node1587 := by
  calc
    injectiveMoment H raw1617 = injectiveMoment H raw1617step0 := by
      have heq : raw1617step0 = (fun i j => raw1617 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1617 permutation39 permutation9
    _ = injectiveMoment H node1587 := by rfl

def raw1618 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw1618step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -2, -1]]

theorem canonical1618 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1618 = injectiveMoment H node1588 := by
  calc
    injectiveMoment H raw1618 = injectiveMoment H raw1618step0 := by
      have heq : raw1618step0 = (fun i j => raw1618 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1618 permutation39 permutation9
    _ = injectiveMoment H node1588 := by rfl

def raw1619 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

theorem canonical1619 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1619 = injectiveMoment H node1606 := by
  rfl

def raw1620 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1620step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical1620 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1620 = injectiveMoment H node2403 := by
  calc
    injectiveMoment H raw1620 = injectiveMoment H raw1620step0 := by
      have heq : raw1620step0 = (fun i j => raw1620 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1620 permutation36 permutation15
    _ = injectiveMoment H node2403 := by rfl

def raw1621 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1621step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical1621 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1621 = injectiveMoment H node775 := by
  calc
    injectiveMoment H raw1621 = injectiveMoment H raw1621step0 := by
      have heq : raw1621step0 = (fun i j => raw1621 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1621 permutation10 permutation15
    _ = injectiveMoment H node775 := by rfl

def raw1622 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw1622step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, -1, -1, 0]]

theorem canonical1622 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1622 = injectiveMoment H node1583 := by
  calc
    injectiveMoment H raw1622 = injectiveMoment H raw1622step0 := by
      have heq : raw1622step0 = (fun i j => raw1622 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1622 permutation41 permutation11
    _ = injectiveMoment H node1583 := by rfl

def raw1623 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw1623step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem canonical1623 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1623 = injectiveMoment H node1602 := by
  calc
    injectiveMoment H raw1623 = injectiveMoment H raw1623step0 := by
      have heq : raw1623step0 = (fun i j => raw1623 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1623 permutation39 permutation11
    _ = injectiveMoment H node1602 := by rfl

def raw1624 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw1624step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical1624 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1624 = injectiveMoment H node1603 := by
  calc
    injectiveMoment H raw1624 = injectiveMoment H raw1624step0 := by
      have heq : raw1624step0 = (fun i j => raw1624 (permutation40 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1624 permutation40 permutation11
    _ = injectiveMoment H node1603 := by rfl

def raw1625 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical1625 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1625 = injectiveMoment H node1607 := by
  rfl

def raw1626 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1626step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical1626 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1626 = injectiveMoment H node2402 := by
  calc
    injectiveMoment H raw1626 = injectiveMoment H raw1626step0 := by
      have heq : raw1626step0 = (fun i j => raw1626 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1626 permutation36 permutation15
    _ = injectiveMoment H node2402 := by rfl

def raw1627 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1627step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical1627 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1627 = injectiveMoment H node774 := by
  calc
    injectiveMoment H raw1627 = injectiveMoment H raw1627step0 := by
      have heq : raw1627step0 = (fun i j => raw1627 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1627 permutation10 permutation15
    _ = injectiveMoment H node774 := by rfl

def raw1628 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical1628 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1628 = injectiveMoment H node1608 := by
  rfl

def raw1629 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw1629step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical1629 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1629 = injectiveMoment H node773 := by
  calc
    injectiveMoment H raw1629 = injectiveMoment H raw1629step0 := by
      have heq : raw1629step0 = (fun i j => raw1629 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1629 permutation10 permutation15
    _ = injectiveMoment H node773 := by rfl

def raw1630 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical1630 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1630 = injectiveMoment H node1609 := by
  rfl

def raw1631 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical1631 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1631 = injectiveMoment H node1610 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
