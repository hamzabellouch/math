import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1888 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 2, -3]]

theorem canonical1888 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1888 = injectiveMoment H node1675 := by
  rfl

def raw1889 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

theorem canonical1889 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1889 = injectiveMoment H node1676 := by
  rfl

def raw1890 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem canonical1890 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1890 = injectiveMoment H node1677 := by
  rfl

def raw1891 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical1891 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1891 = injectiveMoment H node1678 := by
  rfl

def raw1892 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

theorem canonical1892 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1892 = injectiveMoment H node1679 := by
  rfl

def raw1893 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, 0, 1, -3]]

def raw1893step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical1893 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1893 = injectiveMoment H node803 := by
  calc
    injectiveMoment H raw1893 = injectiveMoment H raw1893step0 := by
      have heq : raw1893step0 = (fun i j => raw1893 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1893 permutation10 permutation15
    _ = injectiveMoment H node803 := by rfl

def raw1894 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![2, 0, 0, -2]]

def raw1894step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1894step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

theorem canonical1894 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1894 = injectiveMoment H node1221 := by
  calc
    injectiveMoment H raw1894 = injectiveMoment H raw1894step0 := by
      have hz : ∀ j, raw1894 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw1894step0 = (fun i j => raw1894 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1894 permutation104 hz
    injectiveMoment H raw1894step0 = injectiveMoment H raw1894step1 := by
      have heq : raw1894step1 = (fun i j => raw1894step0 (permutation13 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1894step0 permutation13 permutation17
    _ = injectiveMoment H node1221 := by rfl

def raw1895 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

theorem canonical1895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1895 = injectiveMoment H node1680 := by
  rfl

def raw1896 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw1896step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 1, 0, 1]]

def raw1896step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical1896 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1896 = injectiveMoment H node2742 := by
  calc
    injectiveMoment H raw1896 = injectiveMoment H raw1896step0 := by
      have heq : raw1896step0 = -raw1896 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1896).symm
    injectiveMoment H raw1896step0 = injectiveMoment H raw1896step1 := by
      have heq : raw1896step1 = (fun i j => raw1896step0 (permutation78 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1896step0 permutation78 permutation21
    _ = injectiveMoment H node2742 := by rfl

def raw1897 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -1, 0]]

theorem canonical1897 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1897 = injectiveMoment H node1681 := by
  rfl

def raw1898 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem canonical1898 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1898 = injectiveMoment H node1682 := by
  rfl

def raw1899 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw1899step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 2]]

def raw1899step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical1899 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1899 = injectiveMoment H node2748 := by
  calc
    injectiveMoment H raw1899 = injectiveMoment H raw1899step0 := by
      have heq : raw1899step0 = -raw1899 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1899).symm
    injectiveMoment H raw1899step0 = injectiveMoment H raw1899step1 := by
      have heq : raw1899step1 = (fun i j => raw1899step0 (permutation78 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1899step0 permutation78 permutation21
    _ = injectiveMoment H node2748 := by rfl

def raw1900 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical1900 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1900 = injectiveMoment H node1683 := by
  rfl

def raw1901 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1901step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

theorem canonical1901 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1901 = injectiveMoment H node2708 := by
  calc
    injectiveMoment H raw1901 = injectiveMoment H raw1901step0 := by
      have heq : raw1901step0 = (fun i j => raw1901 (permutation49 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1901 permutation49 permutation17
    _ = injectiveMoment H node2708 := by rfl

def raw1902 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1902step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

theorem canonical1902 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1902 = injectiveMoment H node1221 := by
  calc
    injectiveMoment H raw1902 = injectiveMoment H raw1902step0 := by
      have heq : raw1902step0 = (fun i j => raw1902 (permutation13 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1902 permutation13 permutation17
    _ = injectiveMoment H node1221 := by rfl

def raw1903 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![2, 0, -2, 0]]

def raw1903step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical1903 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1903 = injectiveMoment H node2421 := by
  calc
    injectiveMoment H raw1903 = injectiveMoment H raw1903step0 := by
      have heq : raw1903step0 = (fun i j => raw1903 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1903 permutation36 permutation15
    _ = injectiveMoment H node2421 := by rfl

def raw1904 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw1904step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-2, 1, 0, 1]]

def raw1904step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical1904 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1904 = injectiveMoment H node2742 := by
  calc
    injectiveMoment H raw1904 = injectiveMoment H raw1904step0 := by
      have heq : raw1904step0 = -raw1904 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1904).symm
    injectiveMoment H raw1904step0 = injectiveMoment H raw1904step1 := by
      have heq : raw1904step1 = (fun i j => raw1904step0 (permutation76 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1904step0 permutation76 permutation21
    _ = injectiveMoment H node2742 := by rfl

def raw1905 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw1905step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical1905 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1905 = injectiveMoment H node2676 := by
  calc
    injectiveMoment H raw1905 = injectiveMoment H raw1905step0 := by
      have heq : raw1905step0 = (fun i j => raw1905 (permutation131 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1905 permutation131 permutation23
    _ = injectiveMoment H node2676 := by rfl

def raw1906 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -2, 1]]

theorem canonical1906 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1906 = injectiveMoment H node1684 := by
  rfl

def raw1907 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw1907step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical1907 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1907 = injectiveMoment H node2620 := by
  calc
    injectiveMoment H raw1907 = injectiveMoment H raw1907step0 := by
      have heq : raw1907step0 = (fun i j => raw1907 (permutation107 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1907 permutation107 permutation23
    _ = injectiveMoment H node2620 := by rfl

def raw1908 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw1908step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw1908step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

theorem canonical1908 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1908 = injectiveMoment H node2767 := by
  calc
    injectiveMoment H raw1908 = injectiveMoment H raw1908step0 := by
      have heq : raw1908step0 = -raw1908 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1908).symm
    injectiveMoment H raw1908step0 = injectiveMoment H raw1908step1 := by
      have heq : raw1908step1 = (fun i j => raw1908step0 (permutation64 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1908step0 permutation64 permutation23
    _ = injectiveMoment H node2767 := by rfl

def raw1909 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical1909 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1909 = injectiveMoment H node1685 := by
  rfl

def raw1910 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1910step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical1910 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1910 = injectiveMoment H node2704 := by
  calc
    injectiveMoment H raw1910 = injectiveMoment H raw1910step0 := by
      have heq : raw1910step0 = (fun i j => raw1910 (permutation49 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1910 permutation49 permutation17
    _ = injectiveMoment H node2704 := by rfl

def raw1911 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw1911step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical1911 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1911 = injectiveMoment H node2704 := by
  calc
    injectiveMoment H raw1911 = injectiveMoment H raw1911step0 := by
      have heq : raw1911step0 = (fun i j => raw1911 (permutation55 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1911 permutation55 permutation17
    _ = injectiveMoment H node2704 := by rfl

def raw1912 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1912step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![3, -1, -1, -1]]

def raw1912step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical1912 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1912 = injectiveMoment H node974 := by
  calc
    injectiveMoment H raw1912 = injectiveMoment H raw1912step0 := by
      have heq : raw1912step0 = raw1912.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1912).symm
    injectiveMoment H raw1912step0 = injectiveMoment H raw1912step1 := by
      have heq : raw1912step1 = (fun i j => raw1912step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1912step0 permutation28 permutation24
    _ = injectiveMoment H node974 := by rfl

def raw1913 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw1913step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -2, 1]]

theorem canonical1913 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1913 = injectiveMoment H node1684 := by
  calc
    injectiveMoment H raw1913 = injectiveMoment H raw1913step0 := by
      have heq : raw1913step0 = (fun i j => raw1913 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1913 permutation35 permutation9
    _ = injectiveMoment H node1684 := by rfl

def raw1914 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical1914 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1914 = injectiveMoment H node1686 := by
  rfl

def raw1915 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1915step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical1915 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1915 = injectiveMoment H node2424 := by
  calc
    injectiveMoment H raw1915 = injectiveMoment H raw1915step0 := by
      have heq : raw1915step0 = (fun i j => raw1915 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1915 permutation36 permutation15
    _ = injectiveMoment H node2424 := by rfl

def raw1916 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw1916step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical1916 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1916 = injectiveMoment H node802 := by
  calc
    injectiveMoment H raw1916 = injectiveMoment H raw1916step0 := by
      have heq : raw1916step0 = (fun i j => raw1916 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1916 permutation10 permutation15
    _ = injectiveMoment H node802 := by rfl

def raw1917 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical1917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1917 = injectiveMoment H node1687 := by
  rfl

def raw1918 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical1918 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1918 = injectiveMoment H node1688 := by
  rfl

def raw1919 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def raw1919step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![0, 1, -2, 1], ![3, -1, 0, -2]]

def raw1919step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0]]

theorem canonical1919 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1919 = injectiveMoment H node1223 := by
  calc
    injectiveMoment H raw1919 = injectiveMoment H raw1919step0 := by
      have heq : raw1919step0 = raw1919.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1919).symm
    injectiveMoment H raw1919step0 = injectiveMoment H raw1919step1 := by
      have heq : raw1919step1 = (fun i j => raw1919step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1919step0 permutation27 permutation18
    _ = injectiveMoment H node1223 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
