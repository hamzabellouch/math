import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2304 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw2304step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 2, -1, 0], ![1, 0, 0, -1, 0], ![2, 0, -2, 1, -1]]

def raw2304step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 2, -1, 0], ![1, 0, -1, 0], ![2, -2, 1, -1]]

def raw2304step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical2304 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2304 = injectiveMoment H node837 := by
  calc
    injectiveMoment H raw2304 = injectiveMoment H raw2304step0 := by
      have heq : raw2304step0 = raw2304.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2304).symm
    injectiveMoment H raw2304step0 = injectiveMoment H raw2304step1 := by
      have hz : ∀ i, raw2304step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2304step1 = (fun i j => raw2304step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2304step0 permutation57 hz
    injectiveMoment H raw2304step1 = injectiveMoment H raw2304step2 := by
      have heq : raw2304step2 = (fun i j => raw2304step1 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2304step1 permutation32 permutation30
    _ = injectiveMoment H node837 := by rfl

def raw2305 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw2305step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 2, -1, 0], ![1, 0, 0, 0, -1], ![2, 0, -2, 0, 0]]

def raw2305step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -2, 1, 0], ![-1, 0, 0, 0, 1], ![-2, 0, 2, 0, 0]]

def raw2305step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, 0, 0, 1], ![-2, 2, 0, 0]]

def raw2305step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical2305 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2305 = injectiveMoment H node1053 := by
  calc
    injectiveMoment H raw2305 = injectiveMoment H raw2305step0 := by
      have heq : raw2305step0 = raw2305.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2305).symm
    injectiveMoment H raw2305step0 = injectiveMoment H raw2305step1 := by
      have heq : raw2305step1 = -raw2305step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2305step0).symm
    injectiveMoment H raw2305step1 = injectiveMoment H raw2305step2 := by
      have hz : ∀ i, raw2305step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2305step2 = (fun i j => raw2305step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2305step1 permutation57 hz
    injectiveMoment H raw2305step2 = injectiveMoment H raw2305step3 := by
      have heq : raw2305step3 = (fun i j => raw2305step2 (permutation13 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2305step2 permutation13 permutation32
    _ = injectiveMoment H node1053 := by rfl

def raw2306 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw2306step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 2, -1, 0], ![1, 0, 1, -1, -1], ![2, 0, -3, 1, 0]]

def raw2306step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -2, 1, 0], ![-1, 0, -1, 1, 1], ![-2, 0, 3, -1, 0]]

def raw2306step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, -1, 1, 1], ![-2, 3, -1, 0]]

def raw2306step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

theorem canonical2306 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2306 = injectiveMoment H node1013 := by
  calc
    injectiveMoment H raw2306 = injectiveMoment H raw2306step0 := by
      have heq : raw2306step0 = raw2306.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2306).symm
    injectiveMoment H raw2306step0 = injectiveMoment H raw2306step1 := by
      have heq : raw2306step1 = -raw2306step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2306step0).symm
    injectiveMoment H raw2306step1 = injectiveMoment H raw2306step2 := by
      have hz : ∀ i, raw2306step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2306step2 = (fun i j => raw2306step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2306step1 permutation57 hz
    injectiveMoment H raw2306step2 = injectiveMoment H raw2306step3 := by
      have heq : raw2306step3 = (fun i j => raw2306step2 (permutation13 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2306step2 permutation13 permutation32
    _ = injectiveMoment H node1013 := by rfl

def raw2307 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw2307step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 2, -1, 0], ![1, 0, 1, 0, -2], ![2, 0, -3, 0, 1]]

def raw2307step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, -2, 1, 0], ![-1, 0, -1, 0, 2], ![-2, 0, 3, 0, -1]]

def raw2307step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -2, 1, 0], ![-1, -1, 0, 2], ![-2, 3, 0, -1]]

def raw2307step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

theorem canonical2307 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2307 = injectiveMoment H node1016 := by
  calc
    injectiveMoment H raw2307 = injectiveMoment H raw2307step0 := by
      have heq : raw2307step0 = raw2307.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2307).symm
    injectiveMoment H raw2307step0 = injectiveMoment H raw2307step1 := by
      have heq : raw2307step1 = -raw2307step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2307step0).symm
    injectiveMoment H raw2307step1 = injectiveMoment H raw2307step2 := by
      have hz : ∀ i, raw2307step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw2307step2 = (fun i j => raw2307step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2307step1 permutation57 hz
    injectiveMoment H raw2307step2 = injectiveMoment H raw2307step3 := by
      have heq : raw2307step3 = (fun i j => raw2307step2 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2307step2 permutation14 permutation26
    _ = injectiveMoment H node1016 := by rfl

def raw2308 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw2308step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![1, 0, 0, -1], ![2, 0, -1, -1]]

def raw2308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]

def raw2308step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical2308 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2308 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw2308 = injectiveMoment H raw2308step0 := by
      have heq : raw2308step0 = raw2308.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2308).symm
    injectiveMoment H raw2308step0 = injectiveMoment H raw2308step1 := by
      have hz : ∀ i, raw2308step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw2308step1 = (fun i j => raw2308step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2308step0 permutation15 hz
    injectiveMoment H raw2308step1 = injectiveMoment H raw2308step2 := by
      have heq : raw2308step2 = (fun i j => raw2308step1 (permutation32 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2308step1 permutation32 permutation6
    _ = injectiveMoment H node283 := by rfl

def raw2309 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw2309step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 0, 1, 0], ![1, 1, 0, 0, -2], ![2, -1, 0, -1, 0]]

def raw2309step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![2, -1, -1, 0]]

def raw2309step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical2309 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2309 = injectiveMoment H node1053 := by
  calc
    injectiveMoment H raw2309 = injectiveMoment H raw2309step0 := by
      have heq : raw2309step0 = raw2309.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2309).symm
    injectiveMoment H raw2309step0 = injectiveMoment H raw2309step1 := by
      have hz : ∀ i, raw2309step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw2309step1 = (fun i j => raw2309step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2309step0 permutation80 hz
    injectiveMoment H raw2309step1 = injectiveMoment H raw2309step2 := by
      have heq : raw2309step2 = (fun i j => raw2309step1 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2309step1 permutation28 permutation24
    _ = injectiveMoment H node1053 := by rfl

def raw2310 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw2310step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 0, 0, 1], ![1, 1, 0, -1, -1], ![2, -1, 0, 0, -1]]

def raw2310step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![1, 0, 0, 0, -1], ![-1, -1, 0, 1, 1], ![-2, 1, 0, 0, 1]]

def raw2310step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 0, 0, -1], ![-1, -1, 1, 1], ![-2, 1, 0, 1]]

def raw2310step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical2310 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2310 = injectiveMoment H node1260 := by
  calc
    injectiveMoment H raw2310 = injectiveMoment H raw2310step0 := by
      have heq : raw2310step0 = raw2310.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2310).symm
    injectiveMoment H raw2310step0 = injectiveMoment H raw2310step1 := by
      have heq : raw2310step1 = -raw2310step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2310step0).symm
    injectiveMoment H raw2310step1 = injectiveMoment H raw2310step2 := by
      have hz : ∀ i, raw2310step1 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw2310step2 = (fun i j => raw2310step1 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2310step1 permutation80 hz
    injectiveMoment H raw2310step2 = injectiveMoment H raw2310step3 := by
      have heq : raw2310step3 = (fun i j => raw2310step2 (permutation10 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2310step2 permutation10 permutation24
    _ = injectiveMoment H node1260 := by rfl

def raw2311 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw2311step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 0, 0, 0, 1], ![1, 1, 0, 0, -2], ![2, -1, 0, -1, 0]]

def raw2311step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![2, -1, -1, 0]]

def raw2311step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical2311 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2311 = injectiveMoment H node1047 := by
  calc
    injectiveMoment H raw2311 = injectiveMoment H raw2311step0 := by
      have heq : raw2311step0 = raw2311.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2311).symm
    injectiveMoment H raw2311step0 = injectiveMoment H raw2311step1 := by
      have hz : ∀ i, raw2311step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw2311step1 = (fun i j => raw2311step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2311step0 permutation80 hz
    injectiveMoment H raw2311step1 = injectiveMoment H raw2311step2 := by
      have heq : raw2311step2 = (fun i j => raw2311step1 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2311step1 permutation30 permutation24
    _ = injectiveMoment H node1047 := by rfl

def raw2312 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![2, 1, -2, -1]]

def raw2312step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![2, -1, 0, -1]]

def raw2312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]

def raw2312step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem canonical2312 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2312 = injectiveMoment H node288 := by
  calc
    injectiveMoment H raw2312 = injectiveMoment H raw2312step0 := by
      have heq : raw2312step0 = raw2312.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2312).symm
    injectiveMoment H raw2312step0 = injectiveMoment H raw2312step1 := by
      have hz : ∀ i, raw2312step0 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw2312step1 = (fun i j => raw2312step0 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2312step0 permutation21 hz
    injectiveMoment H raw2312step1 = injectiveMoment H raw2312step2 := by
      have heq : raw2312step2 = (fun i j => raw2312step1 (permutation29 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2312step1 permutation29 permutation6
    _ = injectiveMoment H node288 := by rfl

def raw2313 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical2313 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2313 = injectiveMoment H node1779 := by
  rfl

def raw2314 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

theorem canonical2314 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2314 = injectiveMoment H node1780 := by
  rfl

def raw2315 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

theorem canonical2315 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2315 = injectiveMoment H node1781 := by
  rfl

def raw2316 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

theorem canonical2316 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2316 = injectiveMoment H node1782 := by
  rfl

def raw2317 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem canonical2317 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2317 = injectiveMoment H node1783 := by
  rfl

def raw2318 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical2318 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2318 = injectiveMoment H node1784 := by
  rfl

def raw2319 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw2319step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

theorem canonical2319 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2319 = injectiveMoment H node2450 := by
  calc
    injectiveMoment H raw2319 = injectiveMoment H raw2319step0 := by
      have heq : raw2319step0 = (fun i j => raw2319 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2319 permutation36 permutation15
    _ = injectiveMoment H node2450 := by rfl

def raw2320 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, -1, 1, -2]]

def raw2320step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

theorem canonical2320 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2320 = injectiveMoment H node1780 := by
  calc
    injectiveMoment H raw2320 = injectiveMoment H raw2320step0 := by
      have heq : raw2320step0 = (fun i j => raw2320 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2320 permutation35 permutation9
    _ = injectiveMoment H node1780 := by rfl

def raw2321 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem canonical2321 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2321 = injectiveMoment H node1785 := by
  rfl

def raw2322 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical2322 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2322 = injectiveMoment H node1786 := by
  rfl

def raw2323 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -2, 1]]

theorem canonical2323 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2323 = injectiveMoment H node1787 := by
  rfl

def raw2324 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, 1, 1, -3]]

theorem canonical2324 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2324 = injectiveMoment H node1788 := by
  rfl

def raw2325 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem canonical2325 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2325 = injectiveMoment H node1789 := by
  rfl

def raw2326 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical2326 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2326 = injectiveMoment H node1790 := by
  rfl

def raw2327 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw2327step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem canonical2327 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2327 = injectiveMoment H node1847 := by
  calc
    injectiveMoment H raw2327 = injectiveMoment H raw2327step0 := by
      have heq : raw2327step0 = (fun i j => raw2327 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2327 permutation33 permutation10
    _ = injectiveMoment H node1847 := by rfl

def raw2328 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 0, 0, 0], ![2, 0, -2, 0]]

def raw2328step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-1, 0, 1, 0, 0], ![1, 1, 0, 0, -2], ![2, -1, -1, 0, 0]]

def raw2328step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![2, -1, -1, 0]]

def raw2328step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical2328 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2328 = injectiveMoment H node1053 := by
  calc
    injectiveMoment H raw2328 = injectiveMoment H raw2328step0 := by
      have heq : raw2328step0 = raw2328.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2328).symm
    injectiveMoment H raw2328step0 = injectiveMoment H raw2328step1 := by
      have hz : ∀ i, raw2328step0 i (permutation104 0) = 0 := by decide +kernel
      have heq : raw2328step1 = (fun i j => raw2328step0 i (permutation104 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2328step0 permutation104 hz
    injectiveMoment H raw2328step1 = injectiveMoment H raw2328step2 := by
      have heq : raw2328step2 = (fun i j => raw2328step1 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2328step1 permutation28 permutation24
    _ = injectiveMoment H node1053 := by rfl

def raw2329 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -1, -1, 0]]

def raw2329step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical2329 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2329 = injectiveMoment H node1786 := by
  calc
    injectiveMoment H raw2329 = injectiveMoment H raw2329step0 := by
      have heq : raw2329step0 = (fun i j => raw2329 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2329 permutation35 permutation9
    _ = injectiveMoment H node1786 := by rfl

def raw2330 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

theorem canonical2330 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2330 = injectiveMoment H node1791 := by
  rfl

def raw2331 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical2331 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2331 = injectiveMoment H node1792 := by
  rfl

def raw2332 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical2332 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2332 = injectiveMoment H node1793 := by
  rfl

def raw2333 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -3, 1]]

theorem canonical2333 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2333 = injectiveMoment H node1794 := by
  rfl

def raw2334 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw2334step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical2334 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2334 = injectiveMoment H node2447 := by
  calc
    injectiveMoment H raw2334 = injectiveMoment H raw2334step0 := by
      have heq : raw2334step0 = (fun i j => raw2334 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2334 permutation36 permutation15
    _ = injectiveMoment H node2447 := by rfl

def raw2335 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2335step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical2335 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2335 = injectiveMoment H node2448 := by
  calc
    injectiveMoment H raw2335 = injectiveMoment H raw2335step0 := by
      have heq : raw2335step0 = (fun i j => raw2335 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2335 permutation36 permutation15
    _ = injectiveMoment H node2448 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
