import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1568 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1568step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical1568 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1568 = injectiveMoment H node2401 := by
  calc
    injectiveMoment H raw1568 = injectiveMoment H raw1568step0 := by
      have heq : raw1568step0 = (fun i j => raw1568 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1568 permutation36 permutation15
    _ = injectiveMoment H node2401 := by rfl

def raw1569 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![2, 0, -1, -1]]

def raw1569step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical1569 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1569 = injectiveMoment H node2394 := by
  calc
    injectiveMoment H raw1569 = injectiveMoment H raw1569step0 := by
      have heq : raw1569step0 = (fun i j => raw1569 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1569 permutation36 permutation15
    _ = injectiveMoment H node2394 := by rfl

def raw1570 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 0, 2, -2], ![2, 0, -2, 0]]

def raw1570step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical1570 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1570 = injectiveMoment H node2397 := by
  calc
    injectiveMoment H raw1570 = injectiveMoment H raw1570step0 := by
      have heq : raw1570step0 = (fun i j => raw1570 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1570 permutation36 permutation15
    _ = injectiveMoment H node2397 := by rfl

def raw1571 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw1571step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

theorem canonical1571 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1571 = injectiveMoment H node1548 := by
  calc
    injectiveMoment H raw1571 = injectiveMoment H raw1571step0 := by
      have heq : raw1571step0 = (fun i j => raw1571 (permutation47 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1571 permutation47 permutation11
    _ = injectiveMoment H node1548 := by rfl

def raw1572 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw1572step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical1572 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1572 = injectiveMoment H node2394 := by
  calc
    injectiveMoment H raw1572 = injectiveMoment H raw1572step0 := by
      have heq : raw1572step0 = (fun i j => raw1572 (permutation42 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1572 permutation42 permutation21
    _ = injectiveMoment H node2394 := by rfl

def raw1573 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

theorem canonical1573 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1573 = injectiveMoment H node1590 := by
  rfl

def raw1574 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem canonical1574 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1574 = injectiveMoment H node1591 := by
  rfl

def raw1575 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw1575step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical1575 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1575 = injectiveMoment H node2400 := by
  calc
    injectiveMoment H raw1575 = injectiveMoment H raw1575step0 := by
      have heq : raw1575step0 = (fun i j => raw1575 (permutation42 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1575 permutation42 permutation21
    _ = injectiveMoment H node2400 := by rfl

def raw1576 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical1576 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1576 = injectiveMoment H node1592 := by
  rfl

def raw1577 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, -2, 0]]

theorem canonical1577 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1577 = injectiveMoment H node1593 := by
  rfl

def raw1578 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1578step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical1578 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1578 = injectiveMoment H node2400 := by
  calc
    injectiveMoment H raw1578 = injectiveMoment H raw1578step0 := by
      have heq : raw1578step0 = (fun i j => raw1578 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1578 permutation36 permutation15
    _ = injectiveMoment H node2400 := by rfl

def raw1579 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1579step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical1579 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1579 = injectiveMoment H node2503 := by
  calc
    injectiveMoment H raw1579 = injectiveMoment H raw1579step0 := by
      have heq : raw1579step0 = (fun i j => raw1579 (permutation49 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1579 permutation49 permutation17
    _ = injectiveMoment H node2503 := by rfl

def raw1580 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, -1, 0]]

def raw1580step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical1580 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1580 = injectiveMoment H node2400 := by
  calc
    injectiveMoment H raw1580 = injectiveMoment H raw1580step0 := by
      have heq : raw1580step0 = (fun i j => raw1580 (permutation38 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1580 permutation38 permutation15
    _ = injectiveMoment H node2400 := by rfl

def raw1581 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1581step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical1581 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1581 = injectiveMoment H node915 := by
  calc
    injectiveMoment H raw1581 = injectiveMoment H raw1581step0 := by
      have heq : raw1581step0 = (fun i j => raw1581 (permutation13 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1581 permutation13 permutation17
    _ = injectiveMoment H node915 := by rfl

def raw1582 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw1582step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

theorem canonical1582 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1582 = injectiveMoment H node1590 := by
  calc
    injectiveMoment H raw1582 = injectiveMoment H raw1582step0 := by
      have heq : raw1582step0 = (fun i j => raw1582 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1582 permutation35 permutation9
    _ = injectiveMoment H node1590 := by rfl

def raw1583 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem canonical1583 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1583 = injectiveMoment H node1594 := by
  rfl

def raw1584 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical1584 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1584 = injectiveMoment H node1595 := by
  rfl

def raw1585 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical1585 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1585 = injectiveMoment H node1596 := by
  rfl

def raw1586 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1586step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical1586 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1586 = injectiveMoment H node2399 := by
  calc
    injectiveMoment H raw1586 = injectiveMoment H raw1586step0 := by
      have heq : raw1586step0 = (fun i j => raw1586 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1586 permutation36 permutation15
    _ = injectiveMoment H node2399 := by rfl

def raw1587 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1587step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical1587 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1587 = injectiveMoment H node769 := by
  calc
    injectiveMoment H raw1587 = injectiveMoment H raw1587step0 := by
      have heq : raw1587step0 = (fun i j => raw1587 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1587 permutation10 permutation15
    _ = injectiveMoment H node769 := by rfl

def raw1588 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical1588 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1588 = injectiveMoment H node1597 := by
  rfl

def raw1589 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

theorem canonical1589 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1589 = injectiveMoment H node1598 := by
  rfl

def raw1590 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem canonical1590 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1590 = injectiveMoment H node1599 := by
  rfl

def raw1591 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem canonical1591 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1591 = injectiveMoment H node1600 := by
  rfl

def raw1592 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw1592step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem canonical1592 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1592 = injectiveMoment H node1600 := by
  calc
    injectiveMoment H raw1592 = injectiveMoment H raw1592step0 := by
      have heq : raw1592step0 = (fun i j => raw1592 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1592 permutation34 permutation9
    _ = injectiveMoment H node1600 := by rfl

def raw1593 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 2, -3]]

def raw1593step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![-1, 1, -2, 2], ![4, -1, 0, -3]]

def raw1593step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 2, -1]]

theorem canonical1593 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1593 = injectiveMoment H node1179 := by
  calc
    injectiveMoment H raw1593 = injectiveMoment H raw1593step0 := by
      have heq : raw1593step0 = raw1593.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1593).symm
    injectiveMoment H raw1593step0 = injectiveMoment H raw1593step1 := by
      have heq : raw1593step1 = (fun i j => raw1593step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1593step0 permutation27 permutation18
    _ = injectiveMoment H node1179 := by rfl

def raw1594 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw1594step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical1594 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1594 = injectiveMoment H node1575 := by
  calc
    injectiveMoment H raw1594 = injectiveMoment H raw1594step0 := by
      have heq : raw1594step0 = (fun i j => raw1594 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1594 permutation39 permutation11
    _ = injectiveMoment H node1575 := by rfl

def raw1595 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw1595step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical1595 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1595 = injectiveMoment H node1576 := by
  calc
    injectiveMoment H raw1595 = injectiveMoment H raw1595step0 := by
      have heq : raw1595step0 = (fun i j => raw1595 (permutation40 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1595 permutation40 permutation11
    _ = injectiveMoment H node1576 := by rfl

def raw1596 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem canonical1596 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1596 = injectiveMoment H node1601 := by
  rfl

def raw1597 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, -1, 2, -2]]

def raw1597step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem canonical1597 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1597 = injectiveMoment H node1601 := by
  calc
    injectiveMoment H raw1597 = injectiveMoment H raw1597step0 := by
      have heq : raw1597step0 = (fun i j => raw1597 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1597 permutation34 permutation9
    _ = injectiveMoment H node1601 := by rfl

def raw1598 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, -1, 1, -1]]

def raw1598step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical1598 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1598 = injectiveMoment H node1576 := by
  calc
    injectiveMoment H raw1598 = injectiveMoment H raw1598step0 := by
      have heq : raw1598step0 = (fun i j => raw1598 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1598 permutation39 permutation11
    _ = injectiveMoment H node1576 := by rfl

def raw1599 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 1, -2]]

def raw1599step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![-1, 1, -1, 1], ![4, -1, -1, -2]]

def raw1599step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical1599 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1599 = injectiveMoment H node917 := by
  calc
    injectiveMoment H raw1599 = injectiveMoment H raw1599step0 := by
      have heq : raw1599step0 = raw1599.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1599).symm
    injectiveMoment H raw1599step0 = injectiveMoment H raw1599step1 := by
      have heq : raw1599step1 = (fun i j => raw1599step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1599step0 permutation27 permutation18
    _ = injectiveMoment H node917 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
