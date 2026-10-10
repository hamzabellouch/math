import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2144 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-1, -1, 2, 0], ![3, 2, -3, -2]]

def raw2144step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]

def raw2144step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -2, 3], ![-2, 0, 2]]

def raw2144step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical2144 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2144 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw2144 = injectiveMoment H raw2144step0 := by
      have heq : raw2144step0 = raw2144.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2144).symm
    injectiveMoment H raw2144step0 = injectiveMoment H raw2144step1 := by
      have heq : raw2144step1 = -raw2144step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2144step0).symm
    injectiveMoment H raw2144step1 = injectiveMoment H raw2144step2 := by
      have heq : raw2144step2 = (fun i j => raw2144step1 (permutation26 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2144step1 permutation26 permutation5
    _ = injectiveMoment H node167 := by rfl

def raw2145 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-1, 2, -2, 1], ![3, -1, 1, -3]]

def raw2145step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

theorem canonical2145 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2145 = injectiveMoment H node159 := by
  calc
    injectiveMoment H raw2145 = injectiveMoment H raw2145step0 := by
      have heq : raw2145step0 = raw2145.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2145).symm
    _ = injectiveMoment H node159 := by rfl

def raw2146 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-1, 2, 1, -2], ![3, -1, -2, 0]]

def raw2146step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]

def raw2146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]

def raw2146step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical2146 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2146 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw2146 = injectiveMoment H raw2146step0 := by
      have heq : raw2146step0 = raw2146.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2146).symm
    injectiveMoment H raw2146step0 = injectiveMoment H raw2146step1 := by
      have heq : raw2146step1 = -raw2146step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2146step0).symm
    injectiveMoment H raw2146step1 = injectiveMoment H raw2146step2 := by
      have heq : raw2146step2 = (fun i j => raw2146step1 (permutation13 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2146step1 permutation13 permutation8
    _ = injectiveMoment H node111 := by rfl

def raw2147 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![-1, 3, -2, 0], ![3, -2, 1, -2]]

def raw2147step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -2, 1], ![2, 0, -2]]

def raw2147step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -3, 2], ![-1, 2, -1], ![-2, 0, 2]]

def raw2147step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

theorem canonical2147 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2147 = injectiveMoment H node103 := by
  calc
    injectiveMoment H raw2147 = injectiveMoment H raw2147step0 := by
      have heq : raw2147step0 = raw2147.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2147).symm
    injectiveMoment H raw2147step0 = injectiveMoment H raw2147step1 := by
      have heq : raw2147step1 = -raw2147step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2147step0).symm
    injectiveMoment H raw2147step1 = injectiveMoment H raw2147step2 := by
      have heq : raw2147step2 = (fun i j => raw2147step1 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2147step1 permutation19 permutation5
    _ = injectiveMoment H node103 := by rfl

def raw2148 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw2148step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem canonical2148 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2148 = injectiveMoment H node2204 := by
  calc
    injectiveMoment H raw2148 = injectiveMoment H raw2148step0 := by
      have heq : raw2148step0 = (fun i j => raw2148 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2148 permutation39 permutation11
    _ = injectiveMoment H node2204 := by rfl

def raw2149 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw2149step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem canonical2149 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2149 = injectiveMoment H node2238 := by
  calc
    injectiveMoment H raw2149 = injectiveMoment H raw2149step0 := by
      have heq : raw2149step0 = (fun i j => raw2149 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2149 permutation39 permutation11
    _ = injectiveMoment H node2238 := by rfl

def raw2150 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw2150step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem canonical2150 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2150 = injectiveMoment H node2354 := by
  calc
    injectiveMoment H raw2150 = injectiveMoment H raw2150step0 := by
      have heq : raw2150step0 = (fun i j => raw2150 (permutation33 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2150 permutation33 permutation13
    _ = injectiveMoment H node2354 := by rfl

def raw2151 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 2, 0], ![2, 3, -3, -2]]

def raw2151step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, 2, -3], ![2, 0, -2]]

def raw2151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

theorem canonical2151 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2151 = injectiveMoment H node162 := by
  calc
    injectiveMoment H raw2151 = injectiveMoment H raw2151step0 := by
      have heq : raw2151step0 = raw2151.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2151).symm
    injectiveMoment H raw2151step0 = injectiveMoment H raw2151step1 := by
      have heq : raw2151step1 = (fun i j => raw2151step0 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2151step0 permutation16 permutation5
    _ = injectiveMoment H node162 := by rfl

def raw2152 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -2, 3, -1], ![2, 3, -4, -1]]

def raw2152step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, 3, -4], ![2, -1, -1]]

def raw2152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 2, -3], ![-1, -3, 4], ![-2, 1, 1]]

def raw2152step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

theorem canonical2152 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2152 = injectiveMoment H node84 := by
  calc
    injectiveMoment H raw2152 = injectiveMoment H raw2152step0 := by
      have heq : raw2152step0 = raw2152.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2152).symm
    injectiveMoment H raw2152step0 = injectiveMoment H raw2152step1 := by
      have heq : raw2152step1 = -raw2152step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2152step0).symm
    injectiveMoment H raw2152step1 = injectiveMoment H raw2152step2 := by
      have heq : raw2152step2 = (fun i j => raw2152step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2152step1 permutation22 permutation5
    _ = injectiveMoment H node84 := by rfl

def raw2153 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw2153step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 1, 1, -2], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-2, -1, 0, 3]]

def raw2153step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

theorem canonical2153 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2153 = injectiveMoment H node1627 := by
  calc
    injectiveMoment H raw2153 = injectiveMoment H raw2153step0 := by
      have heq : raw2153step0 = -raw2153 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2153).symm
    injectiveMoment H raw2153step0 = injectiveMoment H raw2153step1 := by
      have heq : raw2153step1 = (fun i j => raw2153step0 (permutation150 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2153step0 permutation150 permutation9
    _ = injectiveMoment H node1627 := by rfl

def raw2154 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

theorem canonical2154 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2154 = injectiveMoment H node1725 := by
  rfl

def raw2155 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem canonical2155 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2155 = injectiveMoment H node1726 := by
  rfl

def raw2156 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem canonical2156 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2156 = injectiveMoment H node1727 := by
  rfl

def raw2157 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

theorem canonical2157 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2157 = injectiveMoment H node1728 := by
  rfl

def raw2158 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw2158step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 1, 1], ![1, -1, -1, 1], ![2, 2, 0, -4]]

def raw2158step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem canonical2158 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2158 = injectiveMoment H node1113 := by
  calc
    injectiveMoment H raw2158 = injectiveMoment H raw2158step0 := by
      have heq : raw2158step0 = raw2158.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2158).symm
    injectiveMoment H raw2158step0 = injectiveMoment H raw2158step1 := by
      have heq : raw2158step1 = (fun i j => raw2158step0 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2158step0 permutation22 permutation23
    _ = injectiveMoment H node1113 := by rfl

def raw2159 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical2159 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2159 = injectiveMoment H node1729 := by
  rfl

def raw2160 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical2160 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2160 = injectiveMoment H node1730 := by
  rfl

def raw2161 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem canonical2161 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2161 = injectiveMoment H node1731 := by
  rfl

def raw2162 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical2162 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2162 = injectiveMoment H node1732 := by
  rfl

def raw2163 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 1, -1, -2]]

theorem canonical2163 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2163 = injectiveMoment H node497 := by
  rfl

def raw2164 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![2, 0, 2, -4]]

theorem canonical2164 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2164 = injectiveMoment H node498 := by
  rfl

def raw2165 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical2165 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2165 = injectiveMoment H node1733 := by
  rfl

def raw2166 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![2, 0, 1, -3]]

def raw2166step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 1, 1, -2], ![0, -2, 1, 1], ![-2, 0, -1, 3]]

def raw2166step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

theorem canonical2166 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2166 = injectiveMoment H node484 := by
  calc
    injectiveMoment H raw2166 = injectiveMoment H raw2166step0 := by
      have heq : raw2166step0 = -raw2166 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2166).symm
    injectiveMoment H raw2166step0 = injectiveMoment H raw2166step1 := by
      have heq : raw2166step1 = (fun i j => raw2166step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2166step0 permutation32 permutation11
    _ = injectiveMoment H node484 := by rfl

def raw2167 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical2167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2167 = injectiveMoment H node1734 := by
  rfl

def raw2168 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw2168step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical2168 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2168 = injectiveMoment H node1059 := by
  calc
    injectiveMoment H raw2168 = injectiveMoment H raw2168step0 := by
      have heq : raw2168step0 = (fun i j => raw2168 (permutation20 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2168 permutation20 permutation23
    _ = injectiveMoment H node1059 := by rfl

def raw2169 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def raw2169step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 1, 1, -2], ![0, -2, -1, 3], ![-2, 0, 1, 1]]

def raw2169step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 1, 0, -2]]

theorem canonical2169 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2169 = injectiveMoment H node488 := by
  calc
    injectiveMoment H raw2169 = injectiveMoment H raw2169step0 := by
      have heq : raw2169step0 = -raw2169 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2169).symm
    injectiveMoment H raw2169step0 = injectiveMoment H raw2169step1 := by
      have heq : raw2169step1 = (fun i j => raw2169step0 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2169step0 permutation25 permutation17
    _ = injectiveMoment H node488 := by rfl

def raw2170 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical2170 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2170 = injectiveMoment H node1735 := by
  rfl

def raw2171 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![2, 0, -2, 0]]

theorem canonical2171 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2171 = injectiveMoment H node499 := by
  rfl

def raw2172 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 2, 1, -4]]

def raw2172step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![1, -1, -1, 1], ![2, 2, 0, -4]]

def raw2172step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical2172 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2172 = injectiveMoment H node1100 := by
  calc
    injectiveMoment H raw2172 = injectiveMoment H raw2172step0 := by
      have heq : raw2172step0 = raw2172.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2172).symm
    injectiveMoment H raw2172step0 = injectiveMoment H raw2172step1 := by
      have heq : raw2172step1 = (fun i j => raw2172step0 (permutation24 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2172step0 permutation24 permutation23
    _ = injectiveMoment H node1100 := by rfl

def raw2173 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 0, -1], ![1, 2, 0, -3]]

def raw2173step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

theorem canonical2173 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2173 = injectiveMoment H node1050 := by
  calc
    injectiveMoment H raw2173 = injectiveMoment H raw2173step0 := by
      have heq : raw2173step0 = (fun i j => raw2173 (permutation18 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2173 permutation18 permutation23
    _ = injectiveMoment H node1050 := by rfl

def raw2174 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 1, -2], ![1, 2, -1, -2]]

theorem canonical2174 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2174 = injectiveMoment H node500 := by
  rfl

def raw2175 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -2, 0], ![1, 1, 2, -4]]

theorem canonical2175 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2175 = injectiveMoment H node501 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
