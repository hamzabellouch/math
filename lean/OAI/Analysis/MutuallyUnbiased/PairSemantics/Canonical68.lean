import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2176 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical2176 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2176 = injectiveMoment H node502 := by
  rfl

def raw2177 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, 1, -3], ![1, 1, -1, -1]]

def raw2177step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical2177 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2177 = injectiveMoment H node502 := by
  calc
    injectiveMoment H raw2177 = injectiveMoment H raw2177step0 := by
      have heq : raw2177step0 = (fun i j => raw2177 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2177 permutation10 permutation9
    _ = injectiveMoment H node502 := by rfl

def raw2178 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 2, -1, -2], ![1, 0, 1, -2]]

def raw2178step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 1, -2], ![1, 2, -1, -2]]

theorem canonical2178 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2178 = injectiveMoment H node500 := by
  calc
    injectiveMoment H raw2178 = injectiveMoment H raw2178step0 := by
      have heq : raw2178step0 = (fun i j => raw2178 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2178 permutation10 permutation9
    _ = injectiveMoment H node500 := by rfl

def raw2179 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 2, 1, -4], ![1, 0, -1, 0]]

def raw2179step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 2, 0], ![1, -1, 1, -1], ![2, 2, -4, 0]]

def raw2179step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical2179 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2179 = injectiveMoment H node1100 := by
  calc
    injectiveMoment H raw2179 = injectiveMoment H raw2179step0 := by
      have heq : raw2179step0 = raw2179.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2179).symm
    injectiveMoment H raw2179step0 = injectiveMoment H raw2179step1 := by
      have heq : raw2179step1 = (fun i j => raw2179step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2179step0 permutation24 permutation29
    _ = injectiveMoment H node1100 := by rfl

def raw2180 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw2180step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical2180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2180 = injectiveMoment H node2762 := by
  calc
    injectiveMoment H raw2180 = injectiveMoment H raw2180step0 := by
      have heq : raw2180step0 = (fun i j => raw2180 (permutation91 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2180 permutation91 permutation23
    _ = injectiveMoment H node2762 := by rfl

def raw2181 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical2181 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2181 = injectiveMoment H node1736 := by
  rfl

def raw2182 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical2182 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2182 = injectiveMoment H node1739 := by
  rfl

def raw2183 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw2183step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem canonical2183 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2183 = injectiveMoment H node2830 := by
  calc
    injectiveMoment H raw2183 = injectiveMoment H raw2183step0 := by
      have heq : raw2183step0 = (fun i j => raw2183 (permutation136 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2183 permutation136 permutation23
    _ = injectiveMoment H node2830 := by rfl

def raw2184 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2184step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -1, 2]]

theorem canonical2184 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2184 = injectiveMoment H node2831 := by
  calc
    injectiveMoment H raw2184 = injectiveMoment H raw2184step0 := by
      have heq : raw2184step0 = (fun i j => raw2184 (permutation89 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2184 permutation89 permutation21
    _ = injectiveMoment H node2831 := by rfl

def raw2185 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw2185step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

theorem canonical2185 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2185 = injectiveMoment H node1316 := by
  calc
    injectiveMoment H raw2185 = injectiveMoment H raw2185step0 := by
      have heq : raw2185step0 = (fun i j => raw2185 (permutation24 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2185 permutation24 permutation21
    _ = injectiveMoment H node1316 := by rfl

def raw2186 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2186step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical2186 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2186 = injectiveMoment H node2814 := by
  calc
    injectiveMoment H raw2186 = injectiveMoment H raw2186step0 := by
      have heq : raw2186step0 = (fun i j => raw2186 (permutation115 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2186 permutation115 permutation23
    _ = injectiveMoment H node2814 := by rfl

def raw2187 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw2187step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical2187 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2187 = injectiveMoment H node1311 := by
  calc
    injectiveMoment H raw2187 = injectiveMoment H raw2187step0 := by
      have heq : raw2187step0 = (fun i j => raw2187 (permutation30 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2187 permutation30 permutation23
    _ = injectiveMoment H node1311 := by rfl

def raw2188 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw2188step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 1, 1], ![1, 0, -2, 1], ![2, 1, 0, -3]]

def raw2188step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 1, -1, -1], ![-1, 0, 2, -1], ![-2, -1, 0, 3]]

def raw2188step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical2188 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2188 = injectiveMoment H node1208 := by
  calc
    injectiveMoment H raw2188 = injectiveMoment H raw2188step0 := by
      have heq : raw2188step0 = raw2188.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2188).symm
    injectiveMoment H raw2188step0 = injectiveMoment H raw2188step1 := by
      have heq : raw2188step1 = -raw2188step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2188step0).symm
    injectiveMoment H raw2188step1 = injectiveMoment H raw2188step2 := by
      have heq : raw2188step2 = (fun i j => raw2188step1 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2188step1 permutation28 permutation17
    _ = injectiveMoment H node1208 := by rfl

def raw2189 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw2189step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

theorem canonical2189 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2189 = injectiveMoment H node3317 := by
  calc
    injectiveMoment H raw2189 = injectiveMoment H raw2189step0 := by
      have heq : raw2189step0 = (fun i j => raw2189 (permutation151 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2189 permutation151 permutation13
    _ = injectiveMoment H node3317 := by rfl

def raw2190 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw2190step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -1, 1]]

theorem canonical2190 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2190 = injectiveMoment H node3320 := by
  calc
    injectiveMoment H raw2190 = injectiveMoment H raw2190step0 := by
      have heq : raw2190step0 = (fun i j => raw2190 (permutation151 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2190 permutation151 permutation13
    _ = injectiveMoment H node3320 := by rfl

def raw2191 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical2191 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2191 = injectiveMoment H node1746 := by
  rfl

def raw2192 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical2192 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2192 = injectiveMoment H node1747 := by
  rfl

def raw2193 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw2193step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw2193step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical2193 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2193 = injectiveMoment H node1747 := by
  calc
    injectiveMoment H raw2193 = injectiveMoment H raw2193step0 := by
      have heq : raw2193step0 = -raw2193 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2193).symm
    injectiveMoment H raw2193step0 = injectiveMoment H raw2193step1 := by
      have heq : raw2193step1 = (fun i j => raw2193step0 (permutation33 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2193step0 permutation33 permutation32
    _ = injectiveMoment H node1747 := by rfl

def raw2194 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical2194 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2194 = injectiveMoment H node1748 := by
  rfl

def raw2195 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical2195 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2195 = injectiveMoment H node1749 := by
  rfl

def raw2196 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical2196 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2196 = injectiveMoment H node1750 := by
  rfl

def raw2197 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical2197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2197 = injectiveMoment H node1751 := by
  rfl

def raw2198 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw2198step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 1, 1], ![1, 1, 0, -2], ![2, 0, -1, -1]]

def raw2198step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

theorem canonical2198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2198 = injectiveMoment H node1263 := by
  calc
    injectiveMoment H raw2198 = injectiveMoment H raw2198step0 := by
      have heq : raw2198step0 = raw2198.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2198).symm
    injectiveMoment H raw2198step0 = injectiveMoment H raw2198step1 := by
      have heq : raw2198step1 = (fun i j => raw2198step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2198step0 permutation28 permutation24
    _ = injectiveMoment H node1263 := by rfl

def raw2199 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical2199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2199 = injectiveMoment H node1752 := by
  rfl

def raw2200 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2200step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 1, -1, 0], ![0, -2, 1, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw2200step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical2200 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2200 = injectiveMoment H node1751 := by
  calc
    injectiveMoment H raw2200 = injectiveMoment H raw2200step0 := by
      have heq : raw2200step0 = -raw2200 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2200).symm
    injectiveMoment H raw2200step0 = injectiveMoment H raw2200step1 := by
      have heq : raw2200step1 = (fun i j => raw2200step0 (permutation36 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2200step0 permutation36 permutation32
    _ = injectiveMoment H node1751 := by rfl

def raw2201 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw2201step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, -1, 2, 0], ![1, 1, -1, -1], ![2, 0, -1, -1]]

def raw2201step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical2201 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2201 = injectiveMoment H node1309 := by
  calc
    injectiveMoment H raw2201 = injectiveMoment H raw2201step0 := by
      have heq : raw2201step0 = raw2201.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2201).symm
    injectiveMoment H raw2201step0 = injectiveMoment H raw2201step1 := by
      have heq : raw2201step1 = (fun i j => raw2201step0 (permutation19 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2201step0 permutation19 permutation20
    _ = injectiveMoment H node1309 := by rfl

def raw2202 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2202step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 1, -1, 0], ![0, -2, 0, 2], ![-1, 0, 1, 0], ![-1, 0, 1, 0]]

def raw2202step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical2202 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2202 = injectiveMoment H node1749 := by
  calc
    injectiveMoment H raw2202 = injectiveMoment H raw2202step0 := by
      have heq : raw2202step0 = -raw2202 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2202).symm
    injectiveMoment H raw2202step0 = injectiveMoment H raw2202step1 := by
      have heq : raw2202step1 = (fun i j => raw2202step0 (permutation36 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2202step0 permutation36 permutation32
    _ = injectiveMoment H node1749 := by rfl

def raw2203 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw2203step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 0, 2], ![1, 1, 0, -2], ![2, 0, -1, -1]]

def raw2203step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical2203 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2203 = injectiveMoment H node1244 := by
  calc
    injectiveMoment H raw2203 = injectiveMoment H raw2203step0 := by
      have heq : raw2203step0 = raw2203.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2203).symm
    injectiveMoment H raw2203step0 = injectiveMoment H raw2203step1 := by
      have heq : raw2203step1 = (fun i j => raw2203step0 (permutation19 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2203step0 permutation19 permutation17
    _ = injectiveMoment H node1244 := by rfl

def raw2204 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def raw2204step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, -1, 1, 1], ![1, 1, -1, -1], ![2, 0, -1, -1]]

def raw2204step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical2204 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2204 = injectiveMoment H node1360 := by
  calc
    injectiveMoment H raw2204 = injectiveMoment H raw2204step0 := by
      have heq : raw2204step0 = raw2204.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2204).symm
    injectiveMoment H raw2204step0 = injectiveMoment H raw2204step1 := by
      have heq : raw2204step1 = (fun i j => raw2204step0 (permutation19 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2204step0 permutation19 permutation18
    _ = injectiveMoment H node1360 := by rfl

def raw2205 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![2, 2, -3, -1]]

def raw2205step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 2, -3], ![2, -1, -1]]

def raw2205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, -2, 3], ![-2, 1, 1]]

def raw2205step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical2205 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2205 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw2205 = injectiveMoment H raw2205step0 := by
      have heq : raw2205step0 = raw2205.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2205).symm
    injectiveMoment H raw2205step0 = injectiveMoment H raw2205step1 := by
      have heq : raw2205step1 = -raw2205step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2205step0).symm
    injectiveMoment H raw2205step1 = injectiveMoment H raw2205step2 := by
      have heq : raw2205step2 = (fun i j => raw2205step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2205step1 permutation22 permutation5
    _ = injectiveMoment H node184 := by rfl

def raw2206 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 3, -2], ![2, 2, -4, 0]]

def raw2206step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![2, -2, 0]]

def raw2206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, -3, 4], ![-2, 2, 0]]

def raw2206step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical2206 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2206 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw2206 = injectiveMoment H raw2206step0 := by
      have heq : raw2206step0 = raw2206.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2206).symm
    injectiveMoment H raw2206step0 = injectiveMoment H raw2206step1 := by
      have heq : raw2206step1 = -raw2206step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2206step0).symm
    injectiveMoment H raw2206step1 = injectiveMoment H raw2206step2 := by
      have heq : raw2206step2 = (fun i j => raw2206step1 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2206step1 permutation21 permutation5
    _ = injectiveMoment H node85 := by rfl

def raw2207 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def raw2207step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -2, 0, 3]]

def raw2207step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -1, -2]]

theorem canonical2207 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2207 = injectiveMoment H node1666 := by
  calc
    injectiveMoment H raw2207 = injectiveMoment H raw2207step0 := by
      have heq : raw2207step0 = -raw2207 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2207).symm
    injectiveMoment H raw2207step0 = injectiveMoment H raw2207step1 := by
      have heq : raw2207step1 = (fun i j => raw2207step0 (permutation142 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2207step0 permutation142 permutation15
    _ = injectiveMoment H node1666 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
