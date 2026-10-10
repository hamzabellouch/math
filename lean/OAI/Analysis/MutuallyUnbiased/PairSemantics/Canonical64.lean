import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2048 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw2048step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, -1, -1, 2], ![3, 0, 0, -3]]

def raw2048step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

theorem canonical2048 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2048 = injectiveMoment H node1063 := by
  calc
    injectiveMoment H raw2048 = injectiveMoment H raw2048step0 := by
      have heq : raw2048step0 = raw2048.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2048).symm
    injectiveMoment H raw2048step0 = injectiveMoment H raw2048step1 := by
      have heq : raw2048step1 = (fun i j => raw2048step0 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2048step0 permutation25 permutation17
    _ = injectiveMoment H node1063 := by rfl

def raw2049 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw2049step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, -1, 0, 1], ![3, 0, -1, -2]]

def raw2049step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2049 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2049 = injectiveMoment H node1202 := by
  calc
    injectiveMoment H raw2049 = injectiveMoment H raw2049step0 := by
      have heq : raw2049step0 = raw2049.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2049).symm
    injectiveMoment H raw2049step0 = injectiveMoment H raw2049step1 := by
      have heq : raw2049step1 = (fun i j => raw2049step0 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2049step0 permutation32 permutation24
    _ = injectiveMoment H node1202 := by rfl

def raw2050 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw2050step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, -1, 1, 0], ![3, 0, -2, -1]]

def raw2050step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2050 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2050 = injectiveMoment H node1202 := by
  calc
    injectiveMoment H raw2050 = injectiveMoment H raw2050step0 := by
      have heq : raw2050step0 = raw2050.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2050).symm
    injectiveMoment H raw2050step0 = injectiveMoment H raw2050step1 := by
      have heq : raw2050step1 = (fun i j => raw2050step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2050step0 permutation32 permutation30
    _ = injectiveMoment H node1202 := by rfl

def raw2051 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, 0, 2, -3], ![1, 0, -1, 0]]

def raw2051step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, -1, 2, -1], ![3, 0, -3, 0]]

def raw2051step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

theorem canonical2051 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2051 = injectiveMoment H node1063 := by
  calc
    injectiveMoment H raw2051 = injectiveMoment H raw2051step0 := by
      have heq : raw2051step0 = raw2051.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2051).symm
    injectiveMoment H raw2051step0 = injectiveMoment H raw2051step1 := by
      have heq : raw2051step1 = (fun i j => raw2051step0 (permutation25 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2051step0 permutation25 permutation19
    _ = injectiveMoment H node1063 := by rfl

def raw2052 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2052step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical2052 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2052 = injectiveMoment H node2427 := by
  calc
    injectiveMoment H raw2052 = injectiveMoment H raw2052step0 := by
      have heq : raw2052step0 = (fun i j => raw2052 (permutation42 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2052 permutation42 permutation15
    _ = injectiveMoment H node2427 := by rfl

def raw2053 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 0, 2, -2], ![2, 0, -2, 0]]

def raw2053step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical2053 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2053 = injectiveMoment H node806 := by
  calc
    injectiveMoment H raw2053 = injectiveMoment H raw2053step0 := by
      have heq : raw2053step0 = (fun i j => raw2053 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2053 permutation12 permutation15
    _ = injectiveMoment H node806 := by rfl

def raw2054 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw2054step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, 1, -1], ![-1, 0, -2, 3]]

def raw2054step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical2054 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2054 = injectiveMoment H node1671 := by
  calc
    injectiveMoment H raw2054 = injectiveMoment H raw2054step0 := by
      have heq : raw2054step0 = -raw2054 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2054).symm
    injectiveMoment H raw2054step0 = injectiveMoment H raw2054step1 := by
      have heq : raw2054step1 = (fun i j => raw2054step0 (permutation134 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2054step0 permutation134 permutation21
    _ = injectiveMoment H node1671 := by rfl

def raw2055 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2055step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw2055step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical2055 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2055 = injectiveMoment H node2580 := by
  calc
    injectiveMoment H raw2055 = injectiveMoment H raw2055step0 := by
      have heq : raw2055step0 = -raw2055 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2055).symm
    injectiveMoment H raw2055step0 = injectiveMoment H raw2055step1 := by
      have heq : raw2055step1 = (fun i j => raw2055step0 (permutation147 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2055step0 permutation147 permutation21
    _ = injectiveMoment H node2580 := by rfl

def raw2056 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2056step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw2056step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical2056 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2056 = injectiveMoment H node2627 := by
  calc
    injectiveMoment H raw2056 = injectiveMoment H raw2056step0 := by
      have heq : raw2056step0 = -raw2056 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2056).symm
    injectiveMoment H raw2056step0 = injectiveMoment H raw2056step1 := by
      have heq : raw2056step1 = (fun i j => raw2056step0 (permutation124 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2056step0 permutation124 permutation21
    _ = injectiveMoment H node2627 := by rfl

def raw2057 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw2057step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem canonical2057 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2057 = injectiveMoment H node1718 := by
  calc
    injectiveMoment H raw2057 = injectiveMoment H raw2057step0 := by
      have heq : raw2057step0 = (fun i j => raw2057 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2057 permutation39 permutation9
    _ = injectiveMoment H node1718 := by rfl

def raw2058 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw2058step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, 0, -1, 1], ![3, -1, 0, -2]]

def raw2058step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![0, 0, 1, -1], ![-3, 1, 0, 2]]

def raw2058step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical2058 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2058 = injectiveMoment H node1109 := by
  calc
    injectiveMoment H raw2058 = injectiveMoment H raw2058step0 := by
      have heq : raw2058step0 = raw2058.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2058).symm
    injectiveMoment H raw2058step0 = injectiveMoment H raw2058step1 := by
      have heq : raw2058step1 = -raw2058step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2058step0).symm
    injectiveMoment H raw2058step1 = injectiveMoment H raw2058step2 := by
      have heq : raw2058step2 = (fun i j => raw2058step1 (permutation15 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2058step1 permutation15 permutation18
    _ = injectiveMoment H node1109 := by rfl

def raw2059 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw2059step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![-1, 0, 1, 0]]

def raw2059step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

theorem canonical2059 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2059 = injectiveMoment H node2640 := by
  calc
    injectiveMoment H raw2059 = injectiveMoment H raw2059step0 := by
      have heq : raw2059step0 = -raw2059 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2059).symm
    injectiveMoment H raw2059step0 = injectiveMoment H raw2059step1 := by
      have heq : raw2059step1 = (fun i j => raw2059step0 (permutation112 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2059step0 permutation112 permutation21
    _ = injectiveMoment H node2640 := by rfl

def raw2060 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

theorem canonical2060 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2060 = injectiveMoment H node1724 := by
  rfl

def raw2061 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2061step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw2061step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical2061 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2061 = injectiveMoment H node2579 := by
  calc
    injectiveMoment H raw2061 = injectiveMoment H raw2061step0 := by
      have heq : raw2061step0 = -raw2061 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2061).symm
    injectiveMoment H raw2061step0 = injectiveMoment H raw2061step1 := by
      have heq : raw2061step1 = (fun i j => raw2061step0 (permutation88 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2061step0 permutation88 permutation23
    _ = injectiveMoment H node2579 := by rfl

def raw2062 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw2062step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, 1, 0, 0]]

def raw2062step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical2062 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2062 = injectiveMoment H node2579 := by
  calc
    injectiveMoment H raw2062 = injectiveMoment H raw2062step0 := by
      have heq : raw2062step0 = -raw2062 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2062).symm
    injectiveMoment H raw2062step0 = injectiveMoment H raw2062step1 := by
      have heq : raw2062step1 = (fun i j => raw2062step0 (permutation90 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2062step0 permutation90 permutation23
    _ = injectiveMoment H node2579 := by rfl

def raw2063 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw2063step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![3, -1, -2, 0]]

def raw2063step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical2063 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2063 = injectiveMoment H node805 := by
  calc
    injectiveMoment H raw2063 = injectiveMoment H raw2063step0 := by
      have heq : raw2063step0 = raw2063.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2063).symm
    injectiveMoment H raw2063step0 = injectiveMoment H raw2063step1 := by
      have heq : raw2063step1 = (fun i j => raw2063step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2063step0 permutation28 permutation18
    _ = injectiveMoment H node805 := by rfl

def raw2064 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2064step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 0, 1, 0]]

def raw2064step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical2064 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2064 = injectiveMoment H node1625 := by
  calc
    injectiveMoment H raw2064 = injectiveMoment H raw2064step0 := by
      have heq : raw2064step0 = -raw2064 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2064).symm
    injectiveMoment H raw2064step0 = injectiveMoment H raw2064step1 := by
      have heq : raw2064step1 = (fun i j => raw2064step0 (permutation87 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2064step0 permutation87 permutation23
    _ = injectiveMoment H node1625 := by rfl

def raw2065 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2065step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 0, 2, -1]]

def raw2065step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, -1, -1]]

theorem canonical2065 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2065 = injectiveMoment H node1623 := by
  calc
    injectiveMoment H raw2065 = injectiveMoment H raw2065step0 := by
      have heq : raw2065step0 = -raw2065 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2065).symm
    injectiveMoment H raw2065step0 = injectiveMoment H raw2065step1 := by
      have heq : raw2065step1 = (fun i j => raw2065step0 (permutation88 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2065step0 permutation88 permutation23
    _ = injectiveMoment H node1623 := by rfl

def raw2066 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw2066step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![0, -1, -2, 3], ![-1, 0, 1, 0], ![-1, 1, 1, -1]]

def raw2066step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical2066 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2066 = injectiveMoment H node1625 := by
  calc
    injectiveMoment H raw2066 = injectiveMoment H raw2066step0 := by
      have heq : raw2066step0 = -raw2066 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2066).symm
    injectiveMoment H raw2066step0 = injectiveMoment H raw2066step1 := by
      have heq : raw2066step1 = (fun i j => raw2066step0 (permutation86 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2066step0 permutation86 permutation23
    _ = injectiveMoment H node1625 := by rfl

def raw2067 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![2, -1, -2, 1]]

def raw2067step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, 0, 2, -2], ![3, -1, -3, 1]]

def raw2067step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -3, 1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 1, -1, -1]]

theorem canonical2067 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2067 = injectiveMoment H node726 := by
  calc
    injectiveMoment H raw2067 = injectiveMoment H raw2067step0 := by
      have heq : raw2067step0 = raw2067.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2067).symm
    injectiveMoment H raw2067step0 = injectiveMoment H raw2067step1 := by
      have heq : raw2067step1 = (fun i j => raw2067step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2067step0 permutation28 permutation18
    _ = injectiveMoment H node726 := by rfl

def raw2068 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw2068step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def raw2068step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical2068 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2068 = injectiveMoment H node933 := by
  calc
    injectiveMoment H raw2068 = injectiveMoment H raw2068step0 := by
      have heq : raw2068step0 = -raw2068 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2068).symm
    injectiveMoment H raw2068step0 = injectiveMoment H raw2068step1 := by
      have heq : raw2068step1 = (fun i j => raw2068step0 (permutation29 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2068step0 permutation29 permutation23
    _ = injectiveMoment H node933 := by rfl

def raw2069 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw2069step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![3, -1, -1, -1]]

def raw2069step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical2069 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2069 = injectiveMoment H node936 := by
  calc
    injectiveMoment H raw2069 = injectiveMoment H raw2069step0 := by
      have heq : raw2069step0 = raw2069.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2069).symm
    injectiveMoment H raw2069step0 = injectiveMoment H raw2069step1 := by
      have heq : raw2069step1 = (fun i j => raw2069step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2069step0 permutation31 permutation20
    _ = injectiveMoment H node936 := by rfl

def raw2070 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, -2, 0]]

def raw2070step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![3, -1, -2, 0]]

def raw2070step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![0, 0, -2, 2], ![-3, 1, 2, 0]]

def raw2070step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 2, -3]]

theorem canonical2070 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2070 = injectiveMoment H node1098 := by
  calc
    injectiveMoment H raw2070 = injectiveMoment H raw2070step0 := by
      have heq : raw2070step0 = raw2070.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2070).symm
    injectiveMoment H raw2070step0 = injectiveMoment H raw2070step1 := by
      have heq : raw2070step1 = -raw2070step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2070step0).symm
    injectiveMoment H raw2070step1 = injectiveMoment H raw2070step2 := by
      have heq : raw2070step2 = (fun i j => raw2070step1 (permutation15 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2070step1 permutation15 permutation20
    _ = injectiveMoment H node1098 := by rfl

def raw2071 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw2071step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical2071 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2071 = injectiveMoment H node1203 := by
  calc
    injectiveMoment H raw2071 = injectiveMoment H raw2071step0 := by
      have heq : raw2071step0 = (fun i j => raw2071 (permutation12 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2071 permutation12 permutation17
    _ = injectiveMoment H node1203 := by rfl

def raw2072 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, -1, 0]]

def raw2072step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical2072 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2072 = injectiveMoment H node1203 := by
  calc
    injectiveMoment H raw2072 = injectiveMoment H raw2072step0 := by
      have heq : raw2072step0 = (fun i j => raw2072 (permutation14 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2072 permutation14 permutation17
    _ = injectiveMoment H node1203 := by rfl

def raw2073 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 0, -2, 1]]

def raw2073step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical2073 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2073 = injectiveMoment H node816 := by
  calc
    injectiveMoment H raw2073 = injectiveMoment H raw2073step0 := by
      have heq : raw2073step0 = (fun i j => raw2073 (permutation14 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2073 permutation14 permutation15
    _ = injectiveMoment H node816 := by rfl

def raw2074 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![0, 1, -2, 1], ![2, -1, 1, -2]]

def raw2074step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

theorem canonical2074 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2074 = injectiveMoment H node484 := by
  calc
    injectiveMoment H raw2074 = injectiveMoment H raw2074step0 := by
      have heq : raw2074step0 = (fun i j => raw2074 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2074 permutation11 permutation9
    _ = injectiveMoment H node484 := by rfl

def raw2075 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2075step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, -1, 2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2075step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical2075 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2075 = injectiveMoment H node2605 := by
  calc
    injectiveMoment H raw2075 = injectiveMoment H raw2075step0 := by
      have heq : raw2075step0 = -raw2075 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2075).symm
    injectiveMoment H raw2075step0 = injectiveMoment H raw2075step1 := by
      have heq : raw2075step1 = (fun i j => raw2075step0 (permutation78 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2075step0 permutation78 permutation23
    _ = injectiveMoment H node2605 := by rfl

def raw2076 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def raw2076step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, -1, 2], ![0, -1, 1, 0], ![-2, 1, 0, 1]]

def raw2076step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical2076 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2076 = injectiveMoment H node1079 := by
  calc
    injectiveMoment H raw2076 = injectiveMoment H raw2076step0 := by
      have heq : raw2076step0 = -raw2076 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2076).symm
    injectiveMoment H raw2076step0 = injectiveMoment H raw2076step1 := by
      have heq : raw2076step1 = (fun i j => raw2076step0 (permutation19 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2076step0 permutation19 permutation23
    _ = injectiveMoment H node1079 := by rfl

def raw2077 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2077step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, -1, 2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw2077step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical2077 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2077 = injectiveMoment H node2579 := by
  calc
    injectiveMoment H raw2077 = injectiveMoment H raw2077step0 := by
      have heq : raw2077step0 = -raw2077 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2077).symm
    injectiveMoment H raw2077step0 = injectiveMoment H raw2077step1 := by
      have heq : raw2077step1 = (fun i j => raw2077step0 (permutation64 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2077step0 permutation64 permutation23
    _ = injectiveMoment H node2579 := by rfl

def raw2078 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw2078step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![3, -2, -1, 0]]

def raw2078step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical2078 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2078 = injectiveMoment H node805 := by
  calc
    injectiveMoment H raw2078 = injectiveMoment H raw2078step0 := by
      have heq : raw2078step0 = raw2078.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2078).symm
    injectiveMoment H raw2078step0 = injectiveMoment H raw2078step1 := by
      have heq : raw2078step1 = (fun i j => raw2078step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2078step0 permutation28 permutation24
    _ = injectiveMoment H node805 := by rfl

def raw2079 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, -1, -2, 1]]

theorem canonical2079 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2079 = injectiveMoment H node489 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
