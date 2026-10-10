import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1760 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

theorem canonical1760 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1760 = injectiveMoment H node1630 := by
  rfl

def raw1761 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

theorem canonical1761 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1761 = injectiveMoment H node1631 := by
  rfl

def raw1762 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

theorem canonical1762 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1762 = injectiveMoment H node1634 := by
  rfl

def raw1763 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical1763 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1763 = injectiveMoment H node1637 := by
  rfl

def raw1764 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1764step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical1764 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1764 = injectiveMoment H node2803 := by
  calc
    injectiveMoment H raw1764 = injectiveMoment H raw1764step0 := by
      have heq : raw1764step0 = (fun i j => raw1764 (permutation83 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1764 permutation83 permutation21
    _ = injectiveMoment H node2803 := by rfl

def raw1765 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1765step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, -1, 0], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, -1, 1, 1]]

def raw1765step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical1765 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1765 = injectiveMoment H node2813 := by
  calc
    injectiveMoment H raw1765 = injectiveMoment H raw1765step0 := by
      have heq : raw1765step0 = -raw1765 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1765).symm
    injectiveMoment H raw1765step0 = injectiveMoment H raw1765step1 := by
      have heq : raw1765step1 = (fun i j => raw1765step0 (permutation70 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1765step0 permutation70 permutation21
    _ = injectiveMoment H node2813 := by rfl

def raw1766 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical1766 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1766 = injectiveMoment H node1644 := by
  rfl

def raw1767 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw1767step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 1, 1], ![0, 1, -2, 1], ![3, 0, 0, -3]]

def raw1767step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

theorem canonical1767 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1767 = injectiveMoment H node1352 := by
  calc
    injectiveMoment H raw1767 = injectiveMoment H raw1767step0 := by
      have heq : raw1767step0 = raw1767.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1767).symm
    injectiveMoment H raw1767step0 = injectiveMoment H raw1767step1 := by
      have heq : raw1767step1 = (fun i j => raw1767step0 (permutation19 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1767step0 permutation19 permutation17
    _ = injectiveMoment H node1352 := by rfl

def raw1768 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw1768step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 1, -1, 0], ![-1, -1, 1, 1], ![-1, -1, 0, 2]]

def raw1768step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical1768 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1768 = injectiveMoment H node1299 := by
  calc
    injectiveMoment H raw1768 = injectiveMoment H raw1768step0 := by
      have heq : raw1768step0 = -raw1768 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1768).symm
    injectiveMoment H raw1768step0 = injectiveMoment H raw1768step1 := by
      have heq : raw1768step1 = (fun i j => raw1768step0 (permutation19 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1768step0 permutation19 permutation21
    _ = injectiveMoment H node1299 := by rfl

def raw1769 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical1769 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1769 = injectiveMoment H node1645 := by
  rfl

def raw1770 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2], ![1, 0, 0, -1]]

def raw1770step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical1770 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1770 = injectiveMoment H node1645 := by
  calc
    injectiveMoment H raw1770 = injectiveMoment H raw1770step0 := by
      have heq : raw1770step0 = (fun i j => raw1770 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1770 permutation34 permutation9
    _ = injectiveMoment H node1645 := by rfl

def raw1771 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

theorem canonical1771 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1771 = injectiveMoment H node471 := by
  rfl

def raw1772 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical1772 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1772 = injectiveMoment H node1646 := by
  rfl

def raw1773 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical1773 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1773 = injectiveMoment H node1647 := by
  rfl

def raw1774 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical1774 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1774 = injectiveMoment H node1648 := by
  rfl

def raw1775 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical1775 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1775 = injectiveMoment H node1649 := by
  rfl

def raw1776 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw1776step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical1776 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1776 = injectiveMoment H node1649 := by
  calc
    injectiveMoment H raw1776 = injectiveMoment H raw1776step0 := by
      have heq : raw1776step0 = (fun i j => raw1776 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1776 permutation34 permutation9
    _ = injectiveMoment H node1649 := by rfl

def raw1777 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw1777step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 1, 1], ![0, 2, -1, -1], ![3, -1, 0, -2]]

def raw1777step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, 1, -1, -1], ![0, -2, 1, 1], ![-3, 1, 0, 2]]

def raw1777step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical1777 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1777 = injectiveMoment H node1347 := by
  calc
    injectiveMoment H raw1777 = injectiveMoment H raw1777step0 := by
      have heq : raw1777step0 = raw1777.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1777).symm
    injectiveMoment H raw1777step0 = injectiveMoment H raw1777step1 := by
      have heq : raw1777step1 = -raw1777step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1777step0).symm
    injectiveMoment H raw1777step1 = injectiveMoment H raw1777step2 := by
      have heq : raw1777step2 = (fun i j => raw1777step1 (permutation16 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1777step1 permutation16 permutation24
    _ = injectiveMoment H node1347 := by rfl

def raw1778 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical1778 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1778 = injectiveMoment H node1650 := by
  rfl

def raw1779 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 1, 0, -2]]

theorem canonical1779 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1779 = injectiveMoment H node1651 := by
  rfl

def raw1780 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical1780 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1780 = injectiveMoment H node1652 := by
  rfl

def raw1781 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical1781 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1781 = injectiveMoment H node1653 := by
  rfl

def raw1782 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -2, 0], ![1, 0, 0, -1]]

def raw1782step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical1782 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1782 = injectiveMoment H node1653 := by
  calc
    injectiveMoment H raw1782 = injectiveMoment H raw1782step0 := by
      have heq : raw1782step0 = (fun i j => raw1782 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1782 permutation34 permutation9
    _ = injectiveMoment H node1653 := by rfl

def raw1783 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 0, -1, 0]]

def raw1783step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical1783 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1783 = injectiveMoment H node1652 := by
  calc
    injectiveMoment H raw1783 = injectiveMoment H raw1783step0 := by
      have heq : raw1783step0 = (fun i j => raw1783 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1783 permutation34 permutation9
    _ = injectiveMoment H node1652 := by rfl

def raw1784 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw1784step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 1, 1], ![0, 2, 0, -2], ![3, -1, -1, -1]]

def raw1784step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

theorem canonical1784 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1784 = injectiveMoment H node975 := by
  calc
    injectiveMoment H raw1784 = injectiveMoment H raw1784step0 := by
      have heq : raw1784step0 = raw1784.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1784).symm
    injectiveMoment H raw1784step0 = injectiveMoment H raw1784step1 := by
      have heq : raw1784step1 = (fun i j => raw1784step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1784step0 permutation28 permutation24
    _ = injectiveMoment H node975 := by rfl

def raw1785 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical1785 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1785 = injectiveMoment H node1654 := by
  rfl

def raw1786 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical1786 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1786 = injectiveMoment H node472 := by
  rfl

def raw1787 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical1787 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1787 = injectiveMoment H node1655 := by
  rfl

def raw1788 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical1788 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1788 = injectiveMoment H node473 := by
  rfl

def raw1789 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

theorem canonical1789 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1789 = injectiveMoment H node1656 := by
  rfl

def raw1790 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical1790 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1790 = injectiveMoment H node1657 := by
  rfl

def raw1791 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

theorem canonical1791 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1791 = injectiveMoment H node474 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
