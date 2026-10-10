import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2240 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw2240step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 1, 1, -3]]

theorem canonical2240 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2240 = injectiveMoment H node2434 := by
  calc
    injectiveMoment H raw2240 = injectiveMoment H raw2240step0 := by
      have heq : raw2240step0 = (fun i j => raw2240 (permutation33 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2240 permutation33 permutation15
    _ = injectiveMoment H node2434 := by rfl

def raw2241 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw2241step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw2241step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical2241 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2241 = injectiveMoment H node837 := by
  calc
    injectiveMoment H raw2241 = injectiveMoment H raw2241step0 := by
      have hz : ∀ j, raw2241 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw2241step0 = (fun i j => raw2241 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2241 permutation80 hz
    injectiveMoment H raw2241step0 = injectiveMoment H raw2241step1 := by
      have heq : raw2241step1 = (fun i j => raw2241step0 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2241step0 permutation10 permutation15
    _ = injectiveMoment H node837 := by rfl

def raw2242 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw2242step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 0, 0, 1], ![1, -1, 0, -1, 1], ![2, 1, 0, 0, -3]]

def raw2242step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![1, -1, -1, 1], ![2, 1, 0, -3]]

def raw2242step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

theorem canonical2242 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2242 = injectiveMoment H node1116 := by
  calc
    injectiveMoment H raw2242 = injectiveMoment H raw2242step0 := by
      have heq : raw2242step0 = raw2242.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2242).symm
    injectiveMoment H raw2242step0 = injectiveMoment H raw2242step1 := by
      have hz : ∀ i, raw2242step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw2242step1 = (fun i j => raw2242step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2242step0 permutation80 hz
    injectiveMoment H raw2242step1 = injectiveMoment H raw2242step2 := by
      have heq : raw2242step2 = (fun i j => raw2242step1 (permutation23 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2242step1 permutation23 permutation17
    _ = injectiveMoment H node1116 := by rfl

def raw2243 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw2243step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw2243step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical2243 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2243 = injectiveMoment H node835 := by
  calc
    injectiveMoment H raw2243 = injectiveMoment H raw2243step0 := by
      have hz : ∀ j, raw2243 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw2243step0 = (fun i j => raw2243 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw2243 permutation80 hz
    injectiveMoment H raw2243step0 = injectiveMoment H raw2243step1 := by
      have heq : raw2243step1 = (fun i j => raw2243step0 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2243step0 permutation9 permutation15
    _ = injectiveMoment H node835 := by rfl

def raw2244 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw2244step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical2244 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2244 = injectiveMoment H node2439 := by
  calc
    injectiveMoment H raw2244 = injectiveMoment H raw2244step0 := by
      have heq : raw2244step0 = (fun i j => raw2244 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2244 permutation34 permutation15
    _ = injectiveMoment H node2439 := by rfl

def raw2245 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw2245step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical2245 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2245 = injectiveMoment H node2438 := by
  calc
    injectiveMoment H raw2245 = injectiveMoment H raw2245step0 := by
      have heq : raw2245step0 = (fun i j => raw2245 (permutation33 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2245 permutation33 permutation15
    _ = injectiveMoment H node2438 := by rfl

def raw2246 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem canonical2246 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2246 = injectiveMoment H node1764 := by
  rfl

def raw2247 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![2, 0, 2, -4]]

def raw2247step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical2247 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2247 = injectiveMoment H node2437 := by
  calc
    injectiveMoment H raw2247 = injectiveMoment H raw2247step0 := by
      have heq : raw2247step0 = (fun i j => raw2247 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2247 permutation36 permutation15
    _ = injectiveMoment H node2437 := by rfl

def raw2248 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![2, 0, 0, -2]]

def raw2248step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical2248 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2248 = injectiveMoment H node2440 := by
  calc
    injectiveMoment H raw2248 = injectiveMoment H raw2248step0 := by
      have heq : raw2248step0 = (fun i j => raw2248 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2248 permutation36 permutation15
    _ = injectiveMoment H node2440 := by rfl

def raw2249 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

theorem canonical2249 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2249 = injectiveMoment H node1765 := by
  rfl

def raw2250 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem canonical2250 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2250 = injectiveMoment H node1766 := by
  rfl

def raw2251 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

theorem canonical2251 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2251 = injectiveMoment H node1767 := by
  rfl

def raw2252 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical2252 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2252 = injectiveMoment H node1768 := by
  rfl

def raw2253 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw2253step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical2253 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2253 = injectiveMoment H node2444 := by
  calc
    injectiveMoment H raw2253 = injectiveMoment H raw2253step0 := by
      have heq : raw2253step0 = (fun i j => raw2253 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2253 permutation36 permutation15
    _ = injectiveMoment H node2444 := by rfl

def raw2254 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw2254step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical2254 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2254 = injectiveMoment H node2445 := by
  calc
    injectiveMoment H raw2254 = injectiveMoment H raw2254step0 := by
      have heq : raw2254step0 = (fun i j => raw2254 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2254 permutation36 permutation15
    _ = injectiveMoment H node2445 := by rfl

def raw2255 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![2, 0, -1, -1]]

def raw2255step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical2255 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2255 = injectiveMoment H node2439 := by
  calc
    injectiveMoment H raw2255 = injectiveMoment H raw2255step0 := by
      have heq : raw2255step0 = (fun i j => raw2255 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2255 permutation36 permutation15
    _ = injectiveMoment H node2439 := by rfl

def raw2256 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2256step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem canonical2256 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2256 = injectiveMoment H node2778 := by
  calc
    injectiveMoment H raw2256 = injectiveMoment H raw2256step0 := by
      have heq : raw2256step0 = (fun i j => raw2256 (permutation77 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2256 permutation77 permutation23
    _ = injectiveMoment H node2778 := by rfl

def raw2257 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

theorem canonical2257 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2257 = injectiveMoment H node1769 := by
  rfl

def raw2258 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem canonical2258 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2258 = injectiveMoment H node1770 := by
  rfl

def raw2259 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical2259 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2259 = injectiveMoment H node1771 := by
  rfl

def raw2260 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw2260step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical2260 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2260 = injectiveMoment H node2443 := by
  calc
    injectiveMoment H raw2260 = injectiveMoment H raw2260step0 := by
      have heq : raw2260step0 = (fun i j => raw2260 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2260 permutation36 permutation15
    _ = injectiveMoment H node2443 := by rfl

def raw2261 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2261step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw2261step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem canonical2261 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2261 = injectiveMoment H node2781 := by
  calc
    injectiveMoment H raw2261 = injectiveMoment H raw2261step0 := by
      have heq : raw2261step0 = -raw2261 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2261).symm
    injectiveMoment H raw2261step0 = injectiveMoment H raw2261step1 := by
      have heq : raw2261step1 = (fun i j => raw2261step0 (permutation97 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2261step0 permutation97 permutation17
    _ = injectiveMoment H node2781 := by rfl

def raw2262 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, -1, 0]]

def raw2262step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical2262 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2262 = injectiveMoment H node2443 := by
  calc
    injectiveMoment H raw2262 = injectiveMoment H raw2262step0 := by
      have heq : raw2262step0 = (fun i j => raw2262 (permutation38 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2262 permutation38 permutation15
    _ = injectiveMoment H node2443 := by rfl

def raw2263 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw2263step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-2, 0, 0, 2]]

def raw2263step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem canonical2263 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2263 = injectiveMoment H node1284 := by
  calc
    injectiveMoment H raw2263 = injectiveMoment H raw2263step0 := by
      have heq : raw2263step0 = -raw2263 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2263).symm
    injectiveMoment H raw2263step0 = injectiveMoment H raw2263step1 := by
      have heq : raw2263step1 = (fun i j => raw2263step0 (permutation26 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2263step0 permutation26 permutation17
    _ = injectiveMoment H node1284 := by rfl

def raw2264 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical2264 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2264 = injectiveMoment H node1772 := by
  rfl

def raw2265 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2265step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2265 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2265 = injectiveMoment H node2442 := by
  calc
    injectiveMoment H raw2265 = injectiveMoment H raw2265step0 := by
      have heq : raw2265step0 = (fun i j => raw2265 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2265 permutation36 permutation15
    _ = injectiveMoment H node2442 := by rfl

def raw2266 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw2266step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2266 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2266 = injectiveMoment H node2442 := by
  calc
    injectiveMoment H raw2266 = injectiveMoment H raw2266step0 := by
      have heq : raw2266step0 = (fun i j => raw2266 (permutation38 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2266 permutation38 permutation15
    _ = injectiveMoment H node2442 := by rfl

def raw2267 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw2267step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical2267 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2267 = injectiveMoment H node837 := by
  calc
    injectiveMoment H raw2267 = injectiveMoment H raw2267step0 := by
      have heq : raw2267step0 = (fun i j => raw2267 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2267 permutation10 permutation15
    _ = injectiveMoment H node837 := by rfl

def raw2268 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2268step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical2268 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2268 = injectiveMoment H node2441 := by
  calc
    injectiveMoment H raw2268 = injectiveMoment H raw2268step0 := by
      have heq : raw2268step0 = (fun i j => raw2268 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2268 permutation36 permutation15
    _ = injectiveMoment H node2441 := by rfl

def raw2269 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical2269 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2269 = injectiveMoment H node1773 := by
  rfl

def raw2270 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical2270 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2270 = injectiveMoment H node1774 := by
  rfl

def raw2271 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, -1, 1, -1]]

def raw2271step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical2271 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2271 = injectiveMoment H node1774 := by
  calc
    injectiveMoment H raw2271 = injectiveMoment H raw2271step0 := by
      have heq : raw2271step0 = (fun i j => raw2271 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2271 permutation34 permutation9
    _ = injectiveMoment H node1774 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
