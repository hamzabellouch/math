import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1824 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def raw1824step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, -2, 3], ![-2, 0, 0, 2]]

def raw1824step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical1824 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1824 = injectiveMoment H node2405 := by
  calc
    injectiveMoment H raw1824 = injectiveMoment H raw1824step0 := by
      have heq : raw1824step0 = -raw1824 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1824).symm
    injectiveMoment H raw1824step0 = injectiveMoment H raw1824step1 := by
      have heq : raw1824step1 = (fun i j => raw1824step0 (permutation125 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1824step0 permutation125 permutation17
    _ = injectiveMoment H node2405 := by rfl

def raw1825 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, -1, 1, -2]]

theorem canonical1825 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1825 = injectiveMoment H node1664 := by
  rfl

def raw1826 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw1826step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 0, 1, 0], ![0, -1, 0, -1, 2], ![3, 1, 0, 0, -4]]

def raw1826step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![0, -1, -1, 2], ![3, 1, 0, -4]]

def raw1826step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical1826 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1826 = injectiveMoment H node1031 := by
  calc
    injectiveMoment H raw1826 = injectiveMoment H raw1826step0 := by
      have heq : raw1826step0 = raw1826.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1826).symm
    injectiveMoment H raw1826step0 = injectiveMoment H raw1826step1 := by
      have hz : ∀ i, raw1826step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw1826step1 = (fun i j => raw1826step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1826step0 permutation80 hz
    injectiveMoment H raw1826step1 = injectiveMoment H raw1826step2 := by
      have heq : raw1826step2 = (fun i j => raw1826step1 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1826step1 permutation21 permutation17
    _ = injectiveMoment H node1031 := by rfl

def raw1827 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 1, -1], ![1, 2, 0, -3]]

def raw1827step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 1, -1, 1], ![-1, -2, 0, 3]]

def raw1827step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![-1, -2, 0, 3]]

def raw1827step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical1827 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1827 = injectiveMoment H node1094 := by
  calc
    injectiveMoment H raw1827 = injectiveMoment H raw1827step0 := by
      have heq : raw1827step0 = -raw1827 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1827).symm
    injectiveMoment H raw1827step0 = injectiveMoment H raw1827step1 := by
      have hz : ∀ j, raw1827step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw1827step1 = (fun i j => raw1827step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1827step0 permutation80 hz
    injectiveMoment H raw1827step1 = injectiveMoment H raw1827step2 := by
      have heq : raw1827step2 = (fun i j => raw1827step1 (permutation25 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1827step1 permutation25 permutation21
    _ = injectiveMoment H node1094 := by rfl

def raw1828 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw1828step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 0, 0, 1], ![0, -1, 0, -1, 2], ![3, 1, 0, 0, -4]]

def raw1828step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![0, -1, -1, 2], ![3, 1, 0, -4]]

def raw1828step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

theorem canonical1828 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1828 = injectiveMoment H node1042 := by
  calc
    injectiveMoment H raw1828 = injectiveMoment H raw1828step0 := by
      have heq : raw1828step0 = raw1828.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1828).symm
    injectiveMoment H raw1828step0 = injectiveMoment H raw1828step1 := by
      have hz : ∀ i, raw1828step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw1828step1 = (fun i j => raw1828step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1828step0 permutation80 hz
    injectiveMoment H raw1828step1 = injectiveMoment H raw1828step2 := by
      have heq : raw1828step2 = (fun i j => raw1828step1 (permutation23 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1828step1 permutation23 permutation17
    _ = injectiveMoment H node1042 := by rfl

def raw1829 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, 1, 0, -3]]

def raw1829step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![2, 1, 0, -3]]

def raw1829step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical1829 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1829 = injectiveMoment H node1197 := by
  calc
    injectiveMoment H raw1829 = injectiveMoment H raw1829step0 := by
      have hz : ∀ j, raw1829 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw1829step0 = (fun i j => raw1829 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1829 permutation104 hz
    injectiveMoment H raw1829step0 = injectiveMoment H raw1829step1 := by
      have heq : raw1829step1 = (fun i j => raw1829step0 (permutation9 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1829step0 permutation9 permutation17
    _ = injectiveMoment H node1197 := by rfl

def raw1830 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, 1, -1, -2]]

def raw1830step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -1, -2]]

theorem canonical1830 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1830 = injectiveMoment H node2407 := by
  calc
    injectiveMoment H raw1830 = injectiveMoment H raw1830step0 := by
      have heq : raw1830step0 = (fun i j => raw1830 (permutation33 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1830 permutation33 permutation15
    _ = injectiveMoment H node2407 := by rfl

def raw1831 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw1831step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical1831 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1831 = injectiveMoment H node2409 := by
  calc
    injectiveMoment H raw1831 = injectiveMoment H raw1831step0 := by
      have heq : raw1831step0 = (fun i j => raw1831 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1831 permutation34 permutation15
    _ = injectiveMoment H node2409 := by rfl

def raw1832 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1832step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical1832 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1832 = injectiveMoment H node2408 := by
  calc
    injectiveMoment H raw1832 = injectiveMoment H raw1832step0 := by
      have heq : raw1832step0 = (fun i j => raw1832 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1832 permutation34 permutation15
    _ = injectiveMoment H node2408 := by rfl

def raw1833 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw1833step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical1833 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1833 = injectiveMoment H node2738 := by
  calc
    injectiveMoment H raw1833 = injectiveMoment H raw1833step0 := by
      have heq : raw1833step0 = (fun i j => raw1833 (permutation60 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1833 permutation60 permutation21
    _ = injectiveMoment H node2738 := by rfl

def raw1834 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, -1, -2]]

theorem canonical1834 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1834 = injectiveMoment H node1665 := by
  rfl

def raw1835 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1835step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical1835 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1835 = injectiveMoment H node2411 := by
  calc
    injectiveMoment H raw1835 = injectiveMoment H raw1835step0 := by
      have heq : raw1835step0 = (fun i j => raw1835 (permutation33 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1835 permutation33 permutation15
    _ = injectiveMoment H node2411 := by rfl

def raw1836 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![2, 1, -1, -2]]

def raw1836step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 2, -1, -2]]

theorem canonical1836 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1836 = injectiveMoment H node796 := by
  calc
    injectiveMoment H raw1836 = injectiveMoment H raw1836step0 := by
      have heq : raw1836step0 = (fun i j => raw1836 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1836 permutation9 permutation15
    _ = injectiveMoment H node796 := by rfl

def raw1837 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![2, 0, 2, -4]]

def raw1837step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 1, 0, 0], ![0, -1, -1, 0, 2], ![3, 1, 0, 0, -4]]

def raw1837step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![0, -1, -1, 2], ![3, 1, 0, -4]]

def raw1837step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical1837 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1837 = injectiveMoment H node1031 := by
  calc
    injectiveMoment H raw1837 = injectiveMoment H raw1837step0 := by
      have heq : raw1837step0 = raw1837.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1837).symm
    injectiveMoment H raw1837step0 = injectiveMoment H raw1837step1 := by
      have hz : ∀ i, raw1837step0 i (permutation104 0) = 0 := by decide +kernel
      have heq : raw1837step1 = (fun i j => raw1837step0 i (permutation104 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1837step0 permutation104 hz
    injectiveMoment H raw1837step1 = injectiveMoment H raw1837step2 := by
      have heq : raw1837step2 = (fun i j => raw1837step1 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1837step1 permutation21 permutation17
    _ = injectiveMoment H node1031 := by rfl

def raw1838 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 2, -2], ![2, 0, 0, -2]]

def raw1838step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical1838 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1838 = injectiveMoment H node2413 := by
  calc
    injectiveMoment H raw1838 = injectiveMoment H raw1838step0 := by
      have heq : raw1838step0 = (fun i j => raw1838 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1838 permutation36 permutation15
    _ = injectiveMoment H node2413 := by rfl

def raw1839 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 3, -4]]

theorem canonical1839 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1839 = injectiveMoment H node1667 := by
  rfl

def raw1840 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -1, 0, -1]]

theorem canonical1840 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1840 = injectiveMoment H node1668 := by
  rfl

def raw1841 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw1841step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, -2, 4]]

def raw1841step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical1841 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1841 = injectiveMoment H node1563 := by
  calc
    injectiveMoment H raw1841 = injectiveMoment H raw1841step0 := by
      have heq : raw1841step0 = -raw1841 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1841).symm
    injectiveMoment H raw1841step0 = injectiveMoment H raw1841step1 := by
      have heq : raw1841step1 = (fun i j => raw1841step0 (permutation146 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1841step0 permutation146 permutation21
    _ = injectiveMoment H node1563 := by rfl

def raw1842 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw1842step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem canonical1842 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1842 = injectiveMoment H node2417 := by
  calc
    injectiveMoment H raw1842 = injectiveMoment H raw1842step0 := by
      have heq : raw1842step0 = (fun i j => raw1842 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1842 permutation36 permutation15
    _ = injectiveMoment H node2417 := by rfl

def raw1843 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def raw1843step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 1, -1, 2]]

def raw1843step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical1843 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1843 = injectiveMoment H node2436 := by
  calc
    injectiveMoment H raw1843 = injectiveMoment H raw1843step0 := by
      have heq : raw1843step0 = -raw1843 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1843).symm
    injectiveMoment H raw1843step0 = injectiveMoment H raw1843step1 := by
      have heq : raw1843step1 = (fun i j => raw1843step0 (permutation143 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1843step0 permutation143 permutation21
    _ = injectiveMoment H node2436 := by rfl

def raw1844 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1844step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical1844 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1844 = injectiveMoment H node2416 := by
  calc
    injectiveMoment H raw1844 = injectiveMoment H raw1844step0 := by
      have heq : raw1844step0 = (fun i j => raw1844 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1844 permutation36 permutation15
    _ = injectiveMoment H node2416 := by rfl

def raw1845 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw1845step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, -1, -1, 2], ![-2, 0, 0, 2]]

def raw1845step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical1845 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1845 = injectiveMoment H node1032 := by
  calc
    injectiveMoment H raw1845 = injectiveMoment H raw1845step0 := by
      have heq : raw1845step0 = -raw1845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1845).symm
    injectiveMoment H raw1845step0 = injectiveMoment H raw1845step1 := by
      have heq : raw1845step1 = (fun i j => raw1845step0 (permutation26 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1845step0 permutation26 permutation17
    _ = injectiveMoment H node1032 := by rfl

def raw1846 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical1846 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1846 = injectiveMoment H node1669 := by
  rfl

def raw1847 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1847step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical1847 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1847 = injectiveMoment H node2415 := by
  calc
    injectiveMoment H raw1847 = injectiveMoment H raw1847step0 := by
      have heq : raw1847step0 = (fun i j => raw1847 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1847 permutation36 permutation15
    _ = injectiveMoment H node2415 := by rfl

def raw1848 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw1848step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical1848 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1848 = injectiveMoment H node2415 := by
  calc
    injectiveMoment H raw1848 = injectiveMoment H raw1848step0 := by
      have heq : raw1848step0 = (fun i j => raw1848 (permutation38 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1848 permutation38 permutation15
    _ = injectiveMoment H node2415 := by rfl

def raw1849 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![2, 0, -1, -1]]

def raw1849step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

theorem canonical1849 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1849 = injectiveMoment H node799 := by
  calc
    injectiveMoment H raw1849 = injectiveMoment H raw1849step0 := by
      have heq : raw1849step0 = (fun i j => raw1849 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1849 permutation10 permutation15
    _ = injectiveMoment H node799 := by rfl

def raw1850 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1850step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical1850 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1850 = injectiveMoment H node2414 := by
  calc
    injectiveMoment H raw1850 = injectiveMoment H raw1850step0 := by
      have heq : raw1850step0 = (fun i j => raw1850 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1850 permutation36 permutation15
    _ = injectiveMoment H node2414 := by rfl

def raw1851 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw1851step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw1851step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical1851 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1851 = injectiveMoment H node2626 := by
  calc
    injectiveMoment H raw1851 = injectiveMoment H raw1851step0 := by
      have heq : raw1851step0 = -raw1851 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1851).symm
    injectiveMoment H raw1851step0 = injectiveMoment H raw1851step1 := by
      have heq : raw1851step1 = (fun i j => raw1851step0 (permutation126 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1851step0 permutation126 permutation21
    _ = injectiveMoment H node2626 := by rfl

def raw1852 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, -1, 1, -2]]

def raw1852step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-2, 1, -1, 2]]

def raw1852step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical1852 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1852 = injectiveMoment H node832 := by
  calc
    injectiveMoment H raw1852 = injectiveMoment H raw1852step0 := by
      have heq : raw1852step0 = -raw1852 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1852).symm
    injectiveMoment H raw1852step0 = injectiveMoment H raw1852step1 := by
      have heq : raw1852step1 = (fun i j => raw1852step0 (permutation31 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1852step0 permutation31 permutation21
    _ = injectiveMoment H node832 := by rfl

def raw1853 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw1853step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, 1, -1], ![0, -2, -1, 3], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw1853step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical1853 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1853 = injectiveMoment H node2416 := by
  calc
    injectiveMoment H raw1853 = injectiveMoment H raw1853step0 := by
      have heq : raw1853step0 = -raw1853 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1853).symm
    injectiveMoment H raw1853step0 = injectiveMoment H raw1853step1 := by
      have heq : raw1853step1 = (fun i j => raw1853step0 (permutation102 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1853step0 permutation102 permutation23
    _ = injectiveMoment H node2416 := by rfl

def raw1854 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical1854 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1854 = injectiveMoment H node1671 := by
  rfl

def raw1855 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw1855step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical1855 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1855 = injectiveMoment H node1671 := by
  calc
    injectiveMoment H raw1855 = injectiveMoment H raw1855step0 := by
      have heq : raw1855step0 = (fun i j => raw1855 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1855 permutation34 permutation9
    _ = injectiveMoment H node1671 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
