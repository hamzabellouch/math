import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1792 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 2, 0, -3]]

theorem canonical1792 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1792 = injectiveMoment H node475 := by
  rfl

def raw1793 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw1793step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![0, 2, -1, -1], ![3, -1, 0, -2]]

def raw1793step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 1, 0, -2], ![0, -2, 1, 1], ![-3, 1, 0, 2]]

def raw1793step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical1793 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1793 = injectiveMoment H node1277 := by
  calc
    injectiveMoment H raw1793 = injectiveMoment H raw1793step0 := by
      have heq : raw1793step0 = raw1793.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1793).symm
    injectiveMoment H raw1793step0 = injectiveMoment H raw1793step1 := by
      have heq : raw1793step1 = -raw1793step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1793step0).symm
    injectiveMoment H raw1793step1 = injectiveMoment H raw1793step2 := by
      have heq : raw1793step2 = (fun i j => raw1793step1 (permutation10 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1793step1 permutation10 permutation24
    _ = injectiveMoment H node1277 := by rfl

def raw1794 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw1794step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![0, 2, 0, -2], ![3, -1, -1, -1]]

def raw1794step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical1794 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1794 = injectiveMoment H node944 := by
  calc
    injectiveMoment H raw1794 = injectiveMoment H raw1794step0 := by
      have heq : raw1794step0 = raw1794.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1794).symm
    injectiveMoment H raw1794step0 = injectiveMoment H raw1794step1 := by
      have heq : raw1794step1 = (fun i j => raw1794step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1794step0 permutation30 permutation24
    _ = injectiveMoment H node944 := by rfl

def raw1795 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical1795 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1795 = injectiveMoment H node476 := by
  rfl

def raw1796 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical1796 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1796 = injectiveMoment H node477 := by
  rfl

def raw1797 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, 0, -2], ![1, 1, -2, 0]]

def raw1797step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical1797 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1797 = injectiveMoment H node476 := by
  calc
    injectiveMoment H raw1797 = injectiveMoment H raw1797step0 := by
      have heq : raw1797step0 = (fun i j => raw1797 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1797 permutation10 permutation9
    _ = injectiveMoment H node476 := by rfl

def raw1798 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 2, -2, -1], ![1, 0, 0, -1]]

def raw1798step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 2, 0], ![0, 2, -2, 0], ![3, -1, -1, -1]]

def raw1798step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical1798 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1798 = injectiveMoment H node944 := by
  calc
    injectiveMoment H raw1798 = injectiveMoment H raw1798step0 := by
      have heq : raw1798step0 = raw1798.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1798).symm
    injectiveMoment H raw1798step0 = injectiveMoment H raw1798step1 := by
      have heq : raw1798step1 = (fun i j => raw1798step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1798step0 permutation30 permutation30
    _ = injectiveMoment H node944 := by rfl

def raw1799 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 2, -1, -2], ![1, 0, -1, 0]]

def raw1799step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 2, 0], ![0, 2, -1, -1], ![3, -1, -2, 0]]

def raw1799step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 1, -2, 0], ![0, -2, 1, 1], ![-3, 1, 2, 0]]

def raw1799step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical1799 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1799 = injectiveMoment H node1277 := by
  calc
    injectiveMoment H raw1799 = injectiveMoment H raw1799step0 := by
      have heq : raw1799step0 = raw1799.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1799).symm
    injectiveMoment H raw1799step0 = injectiveMoment H raw1799step1 := by
      have heq : raw1799step1 = -raw1799step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1799step0).symm
    injectiveMoment H raw1799step1 = injectiveMoment H raw1799step2 := by
      have heq : raw1799step2 = (fun i j => raw1799step1 (permutation10 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1799step1 permutation10 permutation30
    _ = injectiveMoment H node1277 := by rfl

def raw1800 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 2, 0, -3], ![1, 0, -2, 1]]

def raw1800step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 2, 0, -3]]

theorem canonical1800 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1800 = injectiveMoment H node475 := by
  calc
    injectiveMoment H raw1800 = injectiveMoment H raw1800step0 := by
      have heq : raw1800step0 = (fun i j => raw1800 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1800 permutation10 permutation9
    _ = injectiveMoment H node475 := by rfl

def raw1801 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, 1, -4]]

def raw1801step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -2, -1, 4]]

def raw1801step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 2, -3]]

theorem canonical1801 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1801 = injectiveMoment H node1547 := by
  calc
    injectiveMoment H raw1801 = injectiveMoment H raw1801step0 := by
      have heq : raw1801step0 = -raw1801 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1801).symm
    injectiveMoment H raw1801step0 = injectiveMoment H raw1801step1 := by
      have heq : raw1801step1 = (fun i j => raw1801step0 (permutation142 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1801step0 permutation142 permutation17
    _ = injectiveMoment H node1547 := by rfl

def raw1802 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, 0, -3]]

theorem canonical1802 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1802 = injectiveMoment H node1658 := by
  rfl

def raw1803 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, 0, -3]]

theorem canonical1803 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1803 = injectiveMoment H node1659 := by
  rfl

def raw1804 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![2, 1, 0, -3]]

def raw1804step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 2, 0, -3]]

theorem canonical1804 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1804 = injectiveMoment H node789 := by
  calc
    injectiveMoment H raw1804 = injectiveMoment H raw1804step0 := by
      have heq : raw1804step0 = (fun i j => raw1804 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1804 permutation9 permutation15
    _ = injectiveMoment H node789 := by rfl

def raw1805 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 2, -3]]

def raw1805step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 2, -2], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 1, -2, 3]]

def raw1805step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 1, -3]]

theorem canonical1805 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1805 = injectiveMoment H node1491 := by
  calc
    injectiveMoment H raw1805 = injectiveMoment H raw1805step0 := by
      have heq : raw1805step0 = -raw1805 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1805).symm
    injectiveMoment H raw1805step0 = injectiveMoment H raw1805step1 := by
      have heq : raw1805step1 = (fun i j => raw1805step0 (permutation144 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1805step0 permutation144 permutation11
    _ = injectiveMoment H node1491 := by rfl

def raw1806 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

theorem canonical1806 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1806 = injectiveMoment H node1660 := by
  rfl

def raw1807 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, 0, -2]]

theorem canonical1807 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1807 = injectiveMoment H node1661 := by
  rfl

def raw1808 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 0, 0, -1]]

def raw1808step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical1808 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1808 = injectiveMoment H node2406 := by
  calc
    injectiveMoment H raw1808 = injectiveMoment H raw1808step0 := by
      have heq : raw1808step0 = (fun i j => raw1808 (permutation38 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1808 permutation38 permutation15
    _ = injectiveMoment H node2406 := by rfl

def raw1809 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw1809step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

theorem canonical1809 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1809 = injectiveMoment H node1660 := by
  calc
    injectiveMoment H raw1809 = injectiveMoment H raw1809step0 := by
      have heq : raw1809step0 = (fun i j => raw1809 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1809 permutation35 permutation9
    _ = injectiveMoment H node1660 := by rfl

def raw1810 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 0, 1, -3]]

def raw1810step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 1, -2]]

theorem canonical1810 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1810 = injectiveMoment H node794 := by
  calc
    injectiveMoment H raw1810 = injectiveMoment H raw1810step0 := by
      have heq : raw1810step0 = (fun i j => raw1810 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1810 permutation10 permutation15
    _ = injectiveMoment H node794 := by rfl

def raw1811 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def raw1811step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 2, -3]]

theorem canonical1811 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1811 = injectiveMoment H node793 := by
  calc
    injectiveMoment H raw1811 = injectiveMoment H raw1811step0 := by
      have heq : raw1811step0 = (fun i j => raw1811 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1811 permutation10 permutation15
    _ = injectiveMoment H node793 := by rfl

def raw1812 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem canonical1812 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1812 = injectiveMoment H node1662 := by
  rfl

def raw1813 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 2, -3]]

def raw1813step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 2, -2], ![0, -2, 0, 2], ![-2, 1, -2, 3]]

def raw1813step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 1, -3]]

theorem canonical1813 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1813 = injectiveMoment H node406 := by
  calc
    injectiveMoment H raw1813 = injectiveMoment H raw1813step0 := by
      have heq : raw1813step0 = -raw1813 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1813).symm
    injectiveMoment H raw1813step0 = injectiveMoment H raw1813step1 := by
      have heq : raw1813step1 = (fun i j => raw1813step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1813step0 permutation32 permutation11
    _ = injectiveMoment H node406 := by rfl

def raw1814 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical1814 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1814 = injectiveMoment H node1663 := by
  rfl

def raw1815 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![2, -1, 1, -2]]

theorem canonical1815 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1815 = injectiveMoment H node478 := by
  rfl

def raw1816 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 2, 1, -4]]

def raw1816step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![-1, -2, -1, 4]]

def raw1816step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

theorem canonical1816 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1816 = injectiveMoment H node460 := by
  calc
    injectiveMoment H raw1816 = injectiveMoment H raw1816step0 := by
      have heq : raw1816step0 = -raw1816 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1816).symm
    injectiveMoment H raw1816step0 = injectiveMoment H raw1816step1 := by
      have heq : raw1816step1 = (fun i j => raw1816step0 (permutation30 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1816step0 permutation30 permutation15
    _ = injectiveMoment H node460 := by rfl

def raw1817 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 2, 0, -3]]

theorem canonical1817 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1817 = injectiveMoment H node479 := by
  rfl

def raw1818 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, 0, 2, -3], ![1, 1, 0, -2]]

def raw1818step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

theorem canonical1818 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1818 = injectiveMoment H node791 := by
  calc
    injectiveMoment H raw1818 = injectiveMoment H raw1818step0 := by
      have heq : raw1818step0 = (fun i j => raw1818 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1818 permutation9 permutation15
    _ = injectiveMoment H node791 := by rfl

def raw1819 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, 2, 0, -3], ![1, -1, 2, -2]]

def raw1819step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 2, 0, -3]]

theorem canonical1819 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1819 = injectiveMoment H node479 := by
  calc
    injectiveMoment H raw1819 = injectiveMoment H raw1819step0 := by
      have heq : raw1819step0 = (fun i j => raw1819 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1819 permutation10 permutation9
    _ = injectiveMoment H node479 := by rfl

def raw1820 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, 2, 1, -4], ![1, -1, 1, -1]]

def raw1820step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 2, -2], ![-1, -2, -1, 4], ![-1, 1, -1, 1]]

def raw1820step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

theorem canonical1820 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1820 = injectiveMoment H node460 := by
  calc
    injectiveMoment H raw1820 = injectiveMoment H raw1820step0 := by
      have heq : raw1820step0 = -raw1820 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1820).symm
    injectiveMoment H raw1820step0 = injectiveMoment H raw1820step1 := by
      have heq : raw1820step1 = (fun i j => raw1820step0 (permutation24 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1820step0 permutation24 permutation15
    _ = injectiveMoment H node460 := by rfl

def raw1821 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![2, 0, 0, -2]]

def raw1821step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, -2, -1, 3], ![-2, 0, 0, 2]]

def raw1821step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical1821 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1821 = injectiveMoment H node2406 := by
  calc
    injectiveMoment H raw1821 = injectiveMoment H raw1821step0 := by
      have heq : raw1821step0 = -raw1821 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1821).symm
    injectiveMoment H raw1821step0 = injectiveMoment H raw1821step1 := by
      have heq : raw1821step1 = (fun i j => raw1821step0 (permutation126 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1821step0 permutation126 permutation23
    _ = injectiveMoment H node2406 := by rfl

def raw1822 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw1822step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

theorem canonical1822 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1822 = injectiveMoment H node1627 := by
  calc
    injectiveMoment H raw1822 = injectiveMoment H raw1822step0 := by
      have heq : raw1822step0 = (fun i j => raw1822 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1822 permutation39 permutation9
    _ = injectiveMoment H node1627 := by rfl

def raw1823 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw1823step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, -1, 1, 0], ![-2, -1, 0, 3]]

def raw1823step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

theorem canonical1823 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1823 = injectiveMoment H node1629 := by
  calc
    injectiveMoment H raw1823 = injectiveMoment H raw1823step0 := by
      have heq : raw1823step0 = -raw1823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1823).symm
    injectiveMoment H raw1823step0 = injectiveMoment H raw1823step1 := by
      have heq : raw1823step1 = (fun i j => raw1823step0 (permutation148 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1823step0 permutation148 permutation9
    _ = injectiveMoment H node1629 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
