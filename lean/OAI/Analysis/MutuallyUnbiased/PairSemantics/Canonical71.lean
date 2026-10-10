import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2272 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, -1, 1, -2]]

def raw2272step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![1, -1, -1, 1], ![2, 1, -1, -2]]

def raw2272step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 2, -2]]

theorem canonical2272 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2272 = injectiveMoment H node1111 := by
  calc
    injectiveMoment H raw2272 = injectiveMoment H raw2272step0 := by
      have heq : raw2272step0 = raw2272.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2272).symm
    injectiveMoment H raw2272step0 = injectiveMoment H raw2272step1 := by
      have heq : raw2272step1 = (fun i j => raw2272step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2272step0 permutation21 permutation17
    _ = injectiveMoment H node1111 := by rfl

def raw2273 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

theorem canonical2273 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2273 = injectiveMoment H node1775 := by
  rfl

def raw2274 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2274step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical2274 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2274 = injectiveMoment H node2769 := by
  calc
    injectiveMoment H raw2274 = injectiveMoment H raw2274step0 := by
      have heq : raw2274step0 = (fun i j => raw2274 (permutation73 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2274 permutation73 permutation23
    _ = injectiveMoment H node2769 := by rfl

def raw2275 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical2275 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2275 = injectiveMoment H node1776 := by
  rfl

def raw2276 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw2276step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical2276 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2276 = injectiveMoment H node1776 := by
  calc
    injectiveMoment H raw2276 = injectiveMoment H raw2276step0 := by
      have heq : raw2276step0 = (fun i j => raw2276 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2276 permutation34 permutation9
    _ = injectiveMoment H node1776 := by rfl

def raw2277 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def raw2277step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical2277 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2277 = injectiveMoment H node1281 := by
  calc
    injectiveMoment H raw2277 = injectiveMoment H raw2277step0 := by
      have heq : raw2277step0 = (fun i j => raw2277 (permutation20 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2277 permutation20 permutation23
    _ = injectiveMoment H node1281 := by rfl

def raw2278 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2278step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 1, -1], ![0, -2, -1, 3], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw2278step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem canonical2278 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2278 = injectiveMoment H node1718 := by
  calc
    injectiveMoment H raw2278 = injectiveMoment H raw2278step0 := by
      have heq : raw2278step0 = -raw2278 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2278).symm
    injectiveMoment H raw2278step0 = injectiveMoment H raw2278step1 := by
      have heq : raw2278step1 = (fun i j => raw2278step0 (permutation100 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2278step0 permutation100 permutation17
    _ = injectiveMoment H node1718 := by rfl

def raw2279 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical2279 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2279 = injectiveMoment H node1777 := by
  rfl

def raw2280 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem canonical2280 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2280 = injectiveMoment H node1778 := by
  rfl

def raw2281 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw2281step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical2281 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2281 = injectiveMoment H node1777 := by
  calc
    injectiveMoment H raw2281 = injectiveMoment H raw2281step0 := by
      have heq : raw2281step0 = (fun i j => raw2281 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2281 permutation34 permutation9
    _ = injectiveMoment H node1777 := by rfl

def raw2282 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw2282step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![1, -1, -1, 1], ![2, 1, 0, -3]]

def raw2282step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

theorem canonical2282 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2282 = injectiveMoment H node1116 := by
  calc
    injectiveMoment H raw2282 = injectiveMoment H raw2282step0 := by
      have heq : raw2282step0 = raw2282.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2282).symm
    injectiveMoment H raw2282step0 = injectiveMoment H raw2282step1 := by
      have heq : raw2282step1 = (fun i j => raw2282step0 (permutation23 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2282step0 permutation23 permutation17
    _ = injectiveMoment H node1116 := by rfl

def raw2283 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw2283step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 1, -1], ![-1, 0, 0, 1], ![-1, -1, 0, 2]]

def raw2283step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem canonical2283 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2283 = injectiveMoment H node1259 := by
  calc
    injectiveMoment H raw2283 = injectiveMoment H raw2283step0 := by
      have heq : raw2283step0 = -raw2283 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2283).symm
    injectiveMoment H raw2283step0 = injectiveMoment H raw2283step1 := by
      have heq : raw2283step1 = (fun i j => raw2283step0 (permutation32 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2283step0 permutation32 permutation17
    _ = injectiveMoment H node1259 := by rfl

def raw2284 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw2284step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical2284 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2284 = injectiveMoment H node835 := by
  calc
    injectiveMoment H raw2284 = injectiveMoment H raw2284step0 := by
      have heq : raw2284step0 = (fun i j => raw2284 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2284 permutation9 permutation15
    _ = injectiveMoment H node835 := by rfl

def raw2285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 0, 1, -2]]

def raw2285step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical2285 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2285 = injectiveMoment H node835 := by
  calc
    injectiveMoment H raw2285 = injectiveMoment H raw2285step0 := by
      have heq : raw2285step0 = (fun i j => raw2285 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2285 permutation10 permutation15
    _ = injectiveMoment H node835 := by rfl

def raw2286 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw2286step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, -1, 1], ![1, 0, -2, 0, 1], ![2, 0, 1, 0, -3]]

def raw2286step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -1, 1, -1], ![-1, 0, 2, 0, -1], ![-2, 0, -1, 0, 3]]

def raw2286step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-1, 2, 0, -1], ![-2, -1, 0, 3]]

def raw2286step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical2286 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2286 = injectiveMoment H node1249 := by
  calc
    injectiveMoment H raw2286 = injectiveMoment H raw2286step0 := by
      have heq : raw2286step0 = raw2286.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2286).symm
    injectiveMoment H raw2286step0 = injectiveMoment H raw2286step1 := by
      have heq : raw2286step1 = -raw2286step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2286step0).symm
    injectiveMoment H raw2286step1 = injectiveMoment H raw2286step2 := by
      have hz : ∀ i, raw2286step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2286step2 = (fun i j => raw2286step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2286step1 permutation57 hz
    injectiveMoment H raw2286step2 = injectiveMoment H raw2286step3 := by
      have heq : raw2286step3 = (fun i j => raw2286step2 (permutation14 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2286step2 permutation14 permutation24
    _ = injectiveMoment H node1249 := by rfl

def raw2287 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def raw2287step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 1, 1, -1], ![1, 0, -1, -1, 1], ![2, 0, 0, 0, -2]]

def raw2287step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, -1, -1, 1], ![2, 0, 0, -2]]

def raw2287step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical2287 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2287 = injectiveMoment H node1107 := by
  calc
    injectiveMoment H raw2287 = injectiveMoment H raw2287step0 := by
      have heq : raw2287step0 = raw2287.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2287).symm
    injectiveMoment H raw2287step0 = injectiveMoment H raw2287step1 := by
      have hz : ∀ i, raw2287step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2287step1 = (fun i j => raw2287step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2287step0 permutation57 hz
    injectiveMoment H raw2287step1 = injectiveMoment H raw2287step2 := by
      have heq : raw2287step2 = (fun i j => raw2287step1 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2287step1 permutation22 permutation17
    _ = injectiveMoment H node1107 := by rfl

def raw2288 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2288step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 1, 1, -1], ![1, 0, -1, 0, 0], ![2, 0, 0, -1, -1]]

def raw2288step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![1, 0, -1, -1, 1], ![-1, 0, 1, 0, 0], ![-2, 0, 0, 1, 1]]

def raw2288step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![-1, 1, 0, 0], ![-2, 0, 1, 1]]

def raw2288step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2288 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2288 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw2288 = injectiveMoment H raw2288step0 := by
      have heq : raw2288step0 = raw2288.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2288).symm
    injectiveMoment H raw2288step0 = injectiveMoment H raw2288step1 := by
      have heq : raw2288step1 = -raw2288step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2288step0).symm
    injectiveMoment H raw2288step1 = injectiveMoment H raw2288step2 := by
      have hz : ∀ i, raw2288step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2288step2 = (fun i j => raw2288step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2288step1 permutation57 hz
    injectiveMoment H raw2288step2 = injectiveMoment H raw2288step3 := by
      have heq : raw2288step3 = (fun i j => raw2288step2 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2288step2 permutation15 permutation24
    _ = injectiveMoment H node1110 := by rfl

def raw2289 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw2289step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 1, 1, -1], ![1, 0, -1, 1, -1], ![2, 0, 0, -2, 0]]

def raw2289step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![2, 0, -2, 0]]

def raw2289step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical2289 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2289 = injectiveMoment H node1112 := by
  calc
    injectiveMoment H raw2289 = injectiveMoment H raw2289step0 := by
      have heq : raw2289step0 = raw2289.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2289).symm
    injectiveMoment H raw2289step0 = injectiveMoment H raw2289step1 := by
      have hz : ∀ i, raw2289step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2289step1 = (fun i j => raw2289step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2289step0 permutation57 hz
    injectiveMoment H raw2289step1 = injectiveMoment H raw2289step2 := by
      have heq : raw2289step2 = (fun i j => raw2289step1 (permutation25 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2289step1 permutation25 permutation20
    _ = injectiveMoment H node1112 := by rfl

def raw2290 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw2290step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, -1, 1], ![1, 0, -1, -1, 1], ![2, 0, 0, 1, -3]]

def raw2290step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, -1, -1, 1], ![2, 0, 1, -3]]

def raw2290step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical2290 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2290 = injectiveMoment H node1123 := by
  calc
    injectiveMoment H raw2290 = injectiveMoment H raw2290step0 := by
      have heq : raw2290step0 = raw2290.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2290).symm
    injectiveMoment H raw2290step0 = injectiveMoment H raw2290step1 := by
      have hz : ∀ i, raw2290step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2290step1 = (fun i j => raw2290step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2290step0 permutation57 hz
    injectiveMoment H raw2290step1 = injectiveMoment H raw2290step2 := by
      have heq : raw2290step2 = (fun i j => raw2290step1 (permutation25 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2290step1 permutation25 permutation18
    _ = injectiveMoment H node1123 := by rfl

def raw2291 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw2291step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, -1, 1], ![1, 0, -1, 0, 0], ![2, 0, 0, 0, -2]]

def raw2291step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -1, 1, -1], ![-1, 0, 1, 0, 0], ![-2, 0, 0, 0, 2]]

def raw2291step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-2, 0, 0, 2]]

def raw2291step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

theorem canonical2291 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2291 = injectiveMoment H node1265 := by
  calc
    injectiveMoment H raw2291 = injectiveMoment H raw2291step0 := by
      have heq : raw2291step0 = raw2291.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2291).symm
    injectiveMoment H raw2291step0 = injectiveMoment H raw2291step1 := by
      have heq : raw2291step1 = -raw2291step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2291step0).symm
    injectiveMoment H raw2291step1 = injectiveMoment H raw2291step2 := by
      have hz : ∀ i, raw2291step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2291step2 = (fun i j => raw2291step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2291step1 permutation57 hz
    injectiveMoment H raw2291step2 = injectiveMoment H raw2291step3 := by
      have heq : raw2291step3 = (fun i j => raw2291step2 (permutation14 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2291step2 permutation14 permutation24
    _ = injectiveMoment H node1265 := by rfl

def raw2292 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2292step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, 0, 0], ![1, 0, -1, 0, 0], ![2, 0, 0, -1, -1]]

def raw2292step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, -1, 0, 0], ![2, 0, -1, -1]]

def raw2292step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

theorem canonical2292 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2292 = injectiveMoment H node1039 := by
  calc
    injectiveMoment H raw2292 = injectiveMoment H raw2292step0 := by
      have heq : raw2292step0 = raw2292.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2292).symm
    injectiveMoment H raw2292step0 = injectiveMoment H raw2292step1 := by
      have hz : ∀ i, raw2292step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2292step1 = (fun i j => raw2292step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2292step0 permutation57 hz
    injectiveMoment H raw2292step1 = injectiveMoment H raw2292step2 := by
      have heq : raw2292step2 = (fun i j => raw2292step1 (permutation32 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2292step1 permutation32 permutation26
    _ = injectiveMoment H node1039 := by rfl

def raw2293 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw2293step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![1, 0, -1, 0], ![2, 0, 0, -2]]

def raw2293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw2293step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical2293 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2293 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw2293 = injectiveMoment H raw2293step0 := by
      have heq : raw2293step0 = raw2293.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2293).symm
    injectiveMoment H raw2293step0 = injectiveMoment H raw2293step1 := by
      have hz : ∀ i, raw2293step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw2293step1 = (fun i j => raw2293step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2293step0 permutation15 hz
    injectiveMoment H raw2293step1 = injectiveMoment H raw2293step2 := by
      have heq : raw2293step2 = (fun i j => raw2293step1 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2293step1 permutation25 permutation6
    _ = injectiveMoment H node291 := by rfl

def raw2294 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw2294step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 1, 1, -1], ![1, 0, 0, 0, -1], ![2, 0, -1, -1, 0]]

def raw2294step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![1, 0, 0, -1], ![2, -1, -1, 0]]

def raw2294step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical2294 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2294 = injectiveMoment H node1040 := by
  calc
    injectiveMoment H raw2294 = injectiveMoment H raw2294step0 := by
      have heq : raw2294step0 = raw2294.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2294).symm
    injectiveMoment H raw2294step0 = injectiveMoment H raw2294step1 := by
      have hz : ∀ i, raw2294step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2294step1 = (fun i j => raw2294step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2294step0 permutation57 hz
    injectiveMoment H raw2294step1 = injectiveMoment H raw2294step2 := by
      have heq : raw2294step2 = (fun i j => raw2294step1 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2294step1 permutation31 permutation18
    _ = injectiveMoment H node1040 := by rfl

def raw2295 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw2295step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, -1, 1], ![1, 0, 0, 0, -1], ![2, 0, -1, 0, -1]]

def raw2295step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, 0, 0, -1], ![2, -1, 0, -1]]

def raw2295step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical2295 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2295 = injectiveMoment H node1260 := by
  calc
    injectiveMoment H raw2295 = injectiveMoment H raw2295step0 := by
      have heq : raw2295step0 = raw2295.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2295).symm
    injectiveMoment H raw2295step0 = injectiveMoment H raw2295step1 := by
      have hz : ∀ i, raw2295step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2295step1 = (fun i j => raw2295step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2295step0 permutation57 hz
    injectiveMoment H raw2295step1 = injectiveMoment H raw2295step2 := by
      have heq : raw2295step2 = (fun i j => raw2295step1 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2295step1 permutation31 permutation18
    _ = injectiveMoment H node1260 := by rfl

def raw2296 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw2296step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, -1, 1], ![1, 0, 0, 1, -2], ![2, 0, -1, -1, 0]]

def raw2296step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![1, 0, 1, -2], ![2, -1, -1, 0]]

def raw2296step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical2296 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2296 = injectiveMoment H node1078 := by
  calc
    injectiveMoment H raw2296 = injectiveMoment H raw2296step0 := by
      have heq : raw2296step0 = raw2296.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2296).symm
    injectiveMoment H raw2296step0 = injectiveMoment H raw2296step1 := by
      have hz : ∀ i, raw2296step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2296step1 = (fun i j => raw2296step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2296step0 permutation57 hz
    injectiveMoment H raw2296step1 = injectiveMoment H raw2296step2 := by
      have heq : raw2296step2 = (fun i j => raw2296step1 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2296step1 permutation31 permutation18
    _ = injectiveMoment H node1078 := by rfl

def raw2297 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2297step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, 0, 0], ![1, 0, 0, -1, 0], ![2, 0, -1, 0, -1]]

def raw2297step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![1, 0, -1, 0], ![2, -1, 0, -1]]

def raw2297step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2297 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2297 = injectiveMoment H node1044 := by
  calc
    injectiveMoment H raw2297 = injectiveMoment H raw2297step0 := by
      have heq : raw2297step0 = raw2297.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2297).symm
    injectiveMoment H raw2297step0 = injectiveMoment H raw2297step1 := by
      have hz : ∀ i, raw2297step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2297step1 = (fun i j => raw2297step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2297step0 permutation57 hz
    injectiveMoment H raw2297step1 = injectiveMoment H raw2297step2 := by
      have heq : raw2297step2 = (fun i j => raw2297step1 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2297step1 permutation32 permutation30
    _ = injectiveMoment H node1044 := by rfl

def raw2298 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw2298step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![1, 0, 0, -1], ![2, 0, -1, -1]]

def raw2298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw2298step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical2298 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2298 = injectiveMoment H node284 := by
  calc
    injectiveMoment H raw2298 = injectiveMoment H raw2298step0 := by
      have heq : raw2298step0 = raw2298.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2298).symm
    injectiveMoment H raw2298step0 = injectiveMoment H raw2298step1 := by
      have hz : ∀ i, raw2298step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw2298step1 = (fun i j => raw2298step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2298step0 permutation15 hz
    injectiveMoment H raw2298step1 = injectiveMoment H raw2298step2 := by
      have heq : raw2298step2 = (fun i j => raw2298step1 (permutation31 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2298step1 permutation31 permutation6
    _ = injectiveMoment H node284 := by rfl

def raw2299 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw2299step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, -1, 1], ![1, 0, 1, 0, -2], ![2, 0, -2, 0, 0]]

def raw2299step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -1, 1, -1], ![-1, 0, -1, 0, 2], ![-2, 0, 2, 0, 0]]

def raw2299step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![-1, -1, 0, 2], ![-2, 2, 0, 0]]

def raw2299step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical2299 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2299 = injectiveMoment H node1058 := by
  calc
    injectiveMoment H raw2299 = injectiveMoment H raw2299step0 := by
      have heq : raw2299step0 = raw2299.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2299).symm
    injectiveMoment H raw2299step0 = injectiveMoment H raw2299step1 := by
      have heq : raw2299step1 = -raw2299step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2299step0).symm
    injectiveMoment H raw2299step1 = injectiveMoment H raw2299step2 := by
      have hz : ∀ i, raw2299step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2299step2 = (fun i j => raw2299step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2299step1 permutation57 hz
    injectiveMoment H raw2299step2 = injectiveMoment H raw2299step3 := by
      have heq : raw2299step3 = (fun i j => raw2299step2 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2299step2 permutation14 permutation26
    _ = injectiveMoment H node1058 := by rfl

def raw2300 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2300step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 1, 0, 0], ![1, 0, 1, -1, -1], ![2, 0, -2, 0, 0]]

def raw2300step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -1, 0, 0], ![-1, 0, -1, 1, 1], ![-2, 0, 2, 0, 0]]

def raw2300step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 0, 0], ![-1, -1, 1, 1], ![-2, 2, 0, 0]]

def raw2300step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical2300 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2300 = injectiveMoment H node1040 := by
  calc
    injectiveMoment H raw2300 = injectiveMoment H raw2300step0 := by
      have heq : raw2300step0 = raw2300.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2300).symm
    injectiveMoment H raw2300step0 = injectiveMoment H raw2300step1 := by
      have heq : raw2300step1 = -raw2300step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2300step0).symm
    injectiveMoment H raw2300step1 = injectiveMoment H raw2300step2 := by
      have hz : ∀ i, raw2300step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2300step2 = (fun i j => raw2300step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2300step1 permutation57 hz
    injectiveMoment H raw2300step2 = injectiveMoment H raw2300step3 := by
      have heq : raw2300step3 = (fun i j => raw2300step2 (permutation10 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2300step2 permutation10 permutation26
    _ = injectiveMoment H node1040 := by rfl

def raw2301 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw2301step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 2, -1, 0], ![1, 0, -2, 0, 1], ![2, 0, 0, 0, -2]]

def raw2301step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -2, 1, 0], ![-1, 0, 2, 0, -1], ![-2, 0, 0, 0, 2]]

def raw2301step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, 2, 0, -1], ![-2, 0, 0, 2]]

def raw2301step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical2301 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2301 = injectiveMoment H node1010 := by
  calc
    injectiveMoment H raw2301 = injectiveMoment H raw2301step0 := by
      have heq : raw2301step0 = raw2301.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2301).symm
    injectiveMoment H raw2301step0 = injectiveMoment H raw2301step1 := by
      have heq : raw2301step1 = -raw2301step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2301step0).symm
    injectiveMoment H raw2301step1 = injectiveMoment H raw2301step2 := by
      have hz : ∀ i, raw2301step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2301step2 = (fun i j => raw2301step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2301step1 permutation57 hz
    injectiveMoment H raw2301step2 = injectiveMoment H raw2301step3 := by
      have heq : raw2301step3 = (fun i j => raw2301step2 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2301step2 permutation12 permutation26
    _ = injectiveMoment H node1010 := by rfl

def raw2302 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw2302step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 2, -1, 0], ![1, 0, -2, 1, 0], ![2, 0, 0, -1, -1]]

def raw2302step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, -2, 1, 0], ![2, 0, -1, -1]]

def raw2302step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical2302 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2302 = injectiveMoment H node1005 := by
  calc
    injectiveMoment H raw2302 = injectiveMoment H raw2302step0 := by
      have heq : raw2302step0 = raw2302.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2302).symm
    injectiveMoment H raw2302step0 = injectiveMoment H raw2302step1 := by
      have hz : ∀ i, raw2302step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2302step1 = (fun i j => raw2302step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2302step0 permutation57 hz
    injectiveMoment H raw2302step1 = injectiveMoment H raw2302step2 := by
      have heq : raw2302step2 = (fun i j => raw2302step1 (permutation30 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2302step1 permutation30 permutation32
    _ = injectiveMoment H node1005 := by rfl

def raw2303 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2303step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 2, -1, 0], ![1, 0, -1, 0, 0], ![2, 0, -1, 0, -1]]

def raw2303step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -2, 1, 0], ![-1, 0, 1, 0, 0], ![-2, 0, 1, 0, 1]]

def raw2303step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, 1, 0, 0], ![-2, 1, 0, 1]]

def raw2303step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical2303 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2303 = injectiveMoment H node1047 := by
  calc
    injectiveMoment H raw2303 = injectiveMoment H raw2303step0 := by
      have heq : raw2303step0 = raw2303.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2303).symm
    injectiveMoment H raw2303step0 = injectiveMoment H raw2303step1 := by
      have heq : raw2303step1 = -raw2303step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2303step0).symm
    injectiveMoment H raw2303step1 = injectiveMoment H raw2303step2 := by
      have hz : ∀ i, raw2303step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2303step2 = (fun i j => raw2303step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2303step1 permutation57 hz
    injectiveMoment H raw2303step2 = injectiveMoment H raw2303step3 := by
      have heq : raw2303step3 = (fun i j => raw2303step2 (permutation11 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2303step2 permutation11 permutation32
    _ = injectiveMoment H node1047 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
