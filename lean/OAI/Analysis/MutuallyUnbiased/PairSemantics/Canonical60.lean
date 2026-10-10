import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1920 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem canonical1920 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1920 = injectiveMoment H node1689 := by
  rfl

def raw1921 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw1921step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -2, 1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw1921step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical1921 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1921 = injectiveMoment H node2750 := by
  calc
    injectiveMoment H raw1921 = injectiveMoment H raw1921step0 := by
      have heq : raw1921step0 = -raw1921 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1921).symm
    injectiveMoment H raw1921step0 = injectiveMoment H raw1921step1 := by
      have heq : raw1921step1 = (fun i j => raw1921step0 (permutation78 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1921step0 permutation78 permutation21
    _ = injectiveMoment H node2750 := by rfl

def raw1922 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical1922 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1922 = injectiveMoment H node1690 := by
  rfl

def raw1923 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw1923step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical1923 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1923 = injectiveMoment H node1690 := by
  calc
    injectiveMoment H raw1923 = injectiveMoment H raw1923step0 := by
      have heq : raw1923step0 = (fun i j => raw1923 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1923 permutation34 permutation9
    _ = injectiveMoment H node1690 := by rfl

def raw1924 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def raw1924step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![3, -1, -1, -1]]

def raw1924step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical1924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1924 = injectiveMoment H node946 := by
  calc
    injectiveMoment H raw1924 = injectiveMoment H raw1924step0 := by
      have heq : raw1924step0 = raw1924.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1924).symm
    injectiveMoment H raw1924step0 = injectiveMoment H raw1924step1 := by
      have heq : raw1924step1 = (fun i j => raw1924step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1924step0 permutation29 permutation20
    _ = injectiveMoment H node946 := by rfl

def raw1925 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw1925step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical1925 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1925 = injectiveMoment H node2619 := by
  calc
    injectiveMoment H raw1925 = injectiveMoment H raw1925step0 := by
      have heq : raw1925step0 = (fun i j => raw1925 (permutation109 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1925 permutation109 permutation23
    _ = injectiveMoment H node2619 := by rfl

def raw1926 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw1926step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -2, 0, 2], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw1926step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical1926 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1926 = injectiveMoment H node2740 := by
  calc
    injectiveMoment H raw1926 = injectiveMoment H raw1926step0 := by
      have heq : raw1926step0 = -raw1926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1926).symm
    injectiveMoment H raw1926step0 = injectiveMoment H raw1926step1 := by
      have heq : raw1926step1 = (fun i j => raw1926step0 (permutation64 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1926step0 permutation64 permutation23
    _ = injectiveMoment H node2740 := by rfl

def raw1927 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]

theorem canonical1927 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1927 = injectiveMoment H node1691 := by
  rfl

def raw1928 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw1928step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -2, 0, 2], ![-1, 0, 1, 0], ![-1, 1, 0, 0]]

def raw1928step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical1928 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1928 = injectiveMoment H node2740 := by
  calc
    injectiveMoment H raw1928 = injectiveMoment H raw1928step0 := by
      have heq : raw1928step0 = -raw1928 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1928).symm
    injectiveMoment H raw1928step0 = injectiveMoment H raw1928step1 := by
      have heq : raw1928step1 = (fun i j => raw1928step0 (permutation66 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1928step0 permutation66 permutation23
    _ = injectiveMoment H node2740 := by rfl

def raw1929 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, -1, -1, 0]]

def raw1929step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![3, -1, -2, 0]]

def raw1929step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical1929 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1929 = injectiveMoment H node807 := by
  calc
    injectiveMoment H raw1929 = injectiveMoment H raw1929step0 := by
      have heq : raw1929step0 = raw1929.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1929).symm
    injectiveMoment H raw1929step0 = injectiveMoment H raw1929step1 := by
      have heq : raw1929step1 = (fun i j => raw1929step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1929step0 permutation27 permutation18
    _ = injectiveMoment H node807 := by rfl

def raw1930 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw1930step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -2, -1, 3], ![-1, 1, 1, -1], ![-1, 0, 1, 0]]

def raw1930step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, 2, -3], ![1, 1, -1, -1]]

theorem canonical1930 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1930 = injectiveMoment H node1624 := by
  calc
    injectiveMoment H raw1930 = injectiveMoment H raw1930step0 := by
      have heq : raw1930step0 = -raw1930 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1930).symm
    injectiveMoment H raw1930step0 = injectiveMoment H raw1930step1 := by
      have heq : raw1930step1 = (fun i j => raw1930step0 (permutation90 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1930step0 permutation90 permutation17
    _ = injectiveMoment H node1624 := by rfl

def raw1931 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw1931step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -2, -1, 3], ![-1, 1, 0, 0], ![-1, 0, 2, -1]]

def raw1931step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

theorem canonical1931 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1931 = injectiveMoment H node1626 := by
  calc
    injectiveMoment H raw1931 = injectiveMoment H raw1931step0 := by
      have heq : raw1931step0 = -raw1931 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1931).symm
    injectiveMoment H raw1931step0 = injectiveMoment H raw1931step1 := by
      have heq : raw1931step1 = (fun i j => raw1931step0 (permutation91 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1931step0 permutation91 permutation17
    _ = injectiveMoment H node1626 := by rfl

def raw1932 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw1932step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, 0, -1, 1], ![0, -2, -1, 3], ![-1, 0, 1, 0], ![-1, 1, 1, -1]]

def raw1932step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, 2, -3], ![1, 1, -1, -1]]

theorem canonical1932 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1932 = injectiveMoment H node1624 := by
  calc
    injectiveMoment H raw1932 = injectiveMoment H raw1932step0 := by
      have heq : raw1932step0 = -raw1932 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1932).symm
    injectiveMoment H raw1932step0 = injectiveMoment H raw1932step1 := by
      have heq : raw1932step1 = (fun i j => raw1932step0 (permutation88 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1932step0 permutation88 permutation17
    _ = injectiveMoment H node1624 := by rfl

def raw1933 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def raw1933step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical1933 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1933 = injectiveMoment H node1094 := by
  calc
    injectiveMoment H raw1933 = injectiveMoment H raw1933step0 := by
      have heq : raw1933step0 = (fun i j => raw1933 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1933 permutation22 permutation23
    _ = injectiveMoment H node1094 := by rfl

def raw1934 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def raw1934step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![0, 1, 0, -1], ![3, -1, 0, -2]]

def raw1934step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical1934 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1934 = injectiveMoment H node1207 := by
  calc
    injectiveMoment H raw1934 = injectiveMoment H raw1934step0 := by
      have heq : raw1934step0 = raw1934.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1934).symm
    injectiveMoment H raw1934step0 = injectiveMoment H raw1934step1 := by
      have heq : raw1934step1 = (fun i j => raw1934step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1934step0 permutation29 permutation18
    _ = injectiveMoment H node1207 := by rfl

def raw1935 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, -2, -1]]

def raw1935step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![0, 1, 1, -2], ![3, -1, -1, -1]]

def raw1935step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical1935 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1935 = injectiveMoment H node943 := by
  calc
    injectiveMoment H raw1935 = injectiveMoment H raw1935step0 := by
      have heq : raw1935step0 = raw1935.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1935).symm
    injectiveMoment H raw1935step0 = injectiveMoment H raw1935step1 := by
      have heq : raw1935step1 = (fun i j => raw1935step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1935step0 permutation29 permutation18
    _ = injectiveMoment H node943 := by rfl

def raw1936 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1936step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical1936 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1936 = injectiveMoment H node1202 := by
  calc
    injectiveMoment H raw1936 = injectiveMoment H raw1936step0 := by
      have heq : raw1936step0 = (fun i j => raw1936 (permutation11 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1936 permutation11 permutation17
    _ = injectiveMoment H node1202 := by rfl

def raw1937 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1937step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![0, 1, 0, -1], ![3, -1, -1, -1]]

def raw1937step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical1937 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1937 = injectiveMoment H node969 := by
  calc
    injectiveMoment H raw1937 = injectiveMoment H raw1937step0 := by
      have heq : raw1937step0 = raw1937.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1937).symm
    injectiveMoment H raw1937step0 = injectiveMoment H raw1937step1 := by
      have heq : raw1937step1 = (fun i j => raw1937step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1937step0 permutation30 permutation24
    _ = injectiveMoment H node969 := by rfl

def raw1938 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw1938step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical1938 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1938 = injectiveMoment H node801 := by
  calc
    injectiveMoment H raw1938 = injectiveMoment H raw1938step0 := by
      have heq : raw1938step0 = (fun i j => raw1938 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1938 permutation9 permutation15
    _ = injectiveMoment H node801 := by rfl

def raw1939 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw1939step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical1939 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1939 = injectiveMoment H node801 := by
  calc
    injectiveMoment H raw1939 = injectiveMoment H raw1939step0 := by
      have heq : raw1939step0 = (fun i j => raw1939 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1939 permutation10 permutation15
    _ = injectiveMoment H node801 := by rfl

def raw1940 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1940step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical1940 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1940 = injectiveMoment H node2413 := by
  calc
    injectiveMoment H raw1940 = injectiveMoment H raw1940step0 := by
      have heq : raw1940step0 = (fun i j => raw1940 (permutation40 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1940 permutation40 permutation15
    _ = injectiveMoment H node2413 := by rfl

def raw1941 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1941step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical1941 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1941 = injectiveMoment H node2412 := by
  calc
    injectiveMoment H raw1941 = injectiveMoment H raw1941step0 := by
      have heq : raw1941step0 = (fun i j => raw1941 (permutation40 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1941 permutation40 permutation15
    _ = injectiveMoment H node2412 := by rfl

def raw1942 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1942step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical1942 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1942 = injectiveMoment H node2410 := by
  calc
    injectiveMoment H raw1942 = injectiveMoment H raw1942step0 := by
      have heq : raw1942step0 = (fun i j => raw1942 (permutation39 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1942 permutation39 permutation15
    _ = injectiveMoment H node2410 := by rfl

def raw1943 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1943step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical1943 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1943 = injectiveMoment H node2411 := by
  calc
    injectiveMoment H raw1943 = injectiveMoment H raw1943step0 := by
      have heq : raw1943step0 = (fun i j => raw1943 (permutation39 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1943 permutation39 permutation15
    _ = injectiveMoment H node2411 := by rfl

def raw1944 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1944step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1944step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical1944 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1944 = injectiveMoment H node805 := by
  calc
    injectiveMoment H raw1944 = injectiveMoment H raw1944step0 := by
      have hz : ∀ j, raw1944 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw1944step0 = (fun i j => raw1944 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1944 permutation80 hz
    injectiveMoment H raw1944step0 = injectiveMoment H raw1944step1 := by
      have heq : raw1944step1 = (fun i j => raw1944step0 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1944step0 permutation9 permutation15
    _ = injectiveMoment H node805 := by rfl

def raw1945 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

theorem canonical1945 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1945 = injectiveMoment H node1692 := by
  rfl

def raw1946 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

theorem canonical1946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1946 = injectiveMoment H node1693 := by
  rfl

def raw1947 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical1947 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1947 = injectiveMoment H node1694 := by
  rfl

def raw1948 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1948step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

theorem canonical1948 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1948 = injectiveMoment H node2429 := by
  calc
    injectiveMoment H raw1948 = injectiveMoment H raw1948step0 := by
      have heq : raw1948step0 = (fun i j => raw1948 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1948 permutation36 permutation15
    _ = injectiveMoment H node2429 := by rfl

def raw1949 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 0, 0, -2]]

def raw1949step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical1949 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1949 = injectiveMoment H node808 := by
  calc
    injectiveMoment H raw1949 = injectiveMoment H raw1949step0 := by
      have heq : raw1949step0 = (fun i j => raw1949 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1949 permutation10 permutation15
    _ = injectiveMoment H node808 := by rfl

def raw1950 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 0, -1, 1], ![2, 0, 0, -2]]

def raw1950step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical1950 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1950 = injectiveMoment H node2413 := by
  calc
    injectiveMoment H raw1950 = injectiveMoment H raw1950step0 := by
      have heq : raw1950step0 = (fun i j => raw1950 (permutation46 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1950 permutation46 permutation15
    _ = injectiveMoment H node2413 := by rfl

def raw1951 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 0, 0, 0], ![2, 0, -1, -1]]

def raw1951step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def raw1951step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical1951 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1951 = injectiveMoment H node807 := by
  calc
    injectiveMoment H raw1951 = injectiveMoment H raw1951step0 := by
      have hz : ∀ j, raw1951 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw1951step0 = (fun i j => raw1951 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw1951 permutation104 hz
    injectiveMoment H raw1951step0 = injectiveMoment H raw1951step1 := by
      have heq : raw1951step1 = (fun i j => raw1951step0 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1951step0 permutation10 permutation15
    _ = injectiveMoment H node807 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
