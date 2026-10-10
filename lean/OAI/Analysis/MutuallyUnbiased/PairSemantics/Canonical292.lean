import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes54

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9344 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 1, 0], ![1, -2, 1, 0]]

def raw9344step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical9344 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9344 = injectiveMoment H node3207 := by
  calc
    injectiveMoment H raw9344 = injectiveMoment H raw9344step0 := by
      have heq : raw9344step0 = (fun i j => raw9344 (permutation283 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9344 permutation283 permutation14
    _ = injectiveMoment H node3207 := by rfl

def raw9345 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![0, -1, -1, 2]]

def raw9345step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, -3, 4], ![0, 1, 1, -2]]

def raw9345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-1, -3, 4], ![1, 1, -2]]

def raw9345step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical9345 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9345 = injectiveMoment H node253 := by
  calc
    injectiveMoment H raw9345 = injectiveMoment H raw9345step0 := by
      have heq : raw9345step0 = -raw9345 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9345).symm
    injectiveMoment H raw9345step0 = injectiveMoment H raw9345step1 := by
      have hz : ∀ i, raw9345step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9345step1 = (fun i j => raw9345step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9345step0 permutation9 hz
    injectiveMoment H raw9345step1 = injectiveMoment H raw9345step2 := by
      have heq : raw9345step2 = (fun i j => raw9345step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9345step1 permutation21 permutation3
    _ = injectiveMoment H node253 := by rfl

def raw9346 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![0, -2, 3, -1]]

def raw9346step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![-2, 3, -1]]

def raw9346step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical9346 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9346 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw9346 = injectiveMoment H raw9346step0 := by
      have hz : ∀ i, raw9346 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9346step0 = (fun i j => raw9346 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9346 permutation9 hz
    injectiveMoment H raw9346step0 = injectiveMoment H raw9346step1 := by
      have heq : raw9346step1 = (fun i j => raw9346step0 (permutation27 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9346step0 permutation27 permutation4
    _ = injectiveMoment H node176 := by rfl

def raw9347 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![0, -2, 1, 1]]

def raw9347step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -2, -1, 3], ![0, 2, -1, -1]]

def raw9347step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-2, -1, 3], ![2, -1, -1]]

def raw9347step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical9347 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9347 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw9347 = injectiveMoment H raw9347step0 := by
      have heq : raw9347step0 = -raw9347 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9347).symm
    injectiveMoment H raw9347step0 = injectiveMoment H raw9347step1 := by
      have hz : ∀ i, raw9347step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9347step1 = (fun i j => raw9347step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9347step0 permutation9 hz
    injectiveMoment H raw9347step1 = injectiveMoment H raw9347step2 := by
      have heq : raw9347step2 = (fun i j => raw9347step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9347step1 permutation21 permutation3
    _ = injectiveMoment H node176 := by rfl

def raw9348 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, -2, 0, 2]]

def raw9348step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 2, 0, -2]]

def raw9348step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![-2, -2, 4], ![2, 0, -2]]

def raw9348step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical9348 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9348 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw9348 = injectiveMoment H raw9348step0 := by
      have heq : raw9348step0 = -raw9348 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9348).symm
    injectiveMoment H raw9348step0 = injectiveMoment H raw9348step1 := by
      have hz : ∀ i, raw9348step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9348step1 = (fun i j => raw9348step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9348step0 permutation9 hz
    injectiveMoment H raw9348step1 = injectiveMoment H raw9348step2 := by
      have heq : raw9348step2 = (fun i j => raw9348step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9348step1 permutation21 permutation3
    _ = injectiveMoment H node145 := by rfl

def raw9349 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 0, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw9349step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw9349step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

theorem canonical9349 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9349 = injectiveMoment H node3109 := by
  calc
    injectiveMoment H raw9349 = injectiveMoment H raw9349step0 := by
      have heq : raw9349step0 = -raw9349 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9349).symm
    injectiveMoment H raw9349step0 = injectiveMoment H raw9349step1 := by
      have heq : raw9349step1 = (fun i j => raw9349step0 (permutation374 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9349step0 permutation374 permutation15
    _ = injectiveMoment H node3109 := by rfl

def raw9350 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 0, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw9350step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

theorem canonical9350 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9350 = injectiveMoment H node3290 := by
  calc
    injectiveMoment H raw9350 = injectiveMoment H raw9350step0 := by
      have heq : raw9350step0 = (fun i j => raw9350 (permutation221 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9350 permutation221 permutation15
    _ = injectiveMoment H node3290 := by rfl

def raw9351 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw9351step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 1, 0, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw9351step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical9351 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9351 = injectiveMoment H node3120 := by
  calc
    injectiveMoment H raw9351 = injectiveMoment H raw9351step0 := by
      have heq : raw9351step0 = -raw9351 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9351).symm
    injectiveMoment H raw9351step0 = injectiveMoment H raw9351step1 := by
      have heq : raw9351step1 = (fun i j => raw9351step0 (permutation313 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9351step0 permutation313 permutation15
    _ = injectiveMoment H node3120 := by rfl

def raw9352 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![0, 2, 1, -3]]

def raw9352step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![0, -2, -1, 3]]

def raw9352step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical9352 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9352 = injectiveMoment H node3136 := by
  calc
    injectiveMoment H raw9352 = injectiveMoment H raw9352step0 := by
      have heq : raw9352step0 = -raw9352 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9352).symm
    injectiveMoment H raw9352step0 = injectiveMoment H raw9352step1 := by
      have heq : raw9352step1 = (fun i j => raw9352step0 (permutation313 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9352step0 permutation313 permutation15
    _ = injectiveMoment H node3136 := by rfl

def raw9353 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw9353step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical9353 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9353 = injectiveMoment H node3292 := by
  calc
    injectiveMoment H raw9353 = injectiveMoment H raw9353step0 := by
      have heq : raw9353step0 = (fun i j => raw9353 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9353 permutation262 permutation9
    _ = injectiveMoment H node3292 := by rfl

def raw9354 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-1, 0, 2, -1], ![-1, 2, 1, -2]]

def raw9354step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 1, 0, 0], ![1, 0, -2, 1], ![1, -2, -1, 2]]

def raw9354step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical9354 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9354 = injectiveMoment H node3266 := by
  calc
    injectiveMoment H raw9354 = injectiveMoment H raw9354step0 := by
      have heq : raw9354step0 = -raw9354 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9354).symm
    injectiveMoment H raw9354step0 = injectiveMoment H raw9354step1 := by
      have heq : raw9354step1 = (fun i j => raw9354step0 (permutation313 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9354step0 permutation313 permutation15
    _ = injectiveMoment H node3266 := by rfl

def raw9355 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-1, 1, 1, -1], ![-1, 1, 2, -2]]

def raw9355step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical9355 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9355 = injectiveMoment H node3462 := by
  calc
    injectiveMoment H raw9355 = injectiveMoment H raw9355step0 := by
      have heq : raw9355step0 = (fun i j => raw9355 (permutation396 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9355 permutation396 permutation10
    _ = injectiveMoment H node3462 := by rfl

def raw9356 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![0, 0, 2, -2], ![-2, 2, 1, -1]]

def raw9356step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical9356 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9356 = injectiveMoment H node3315 := by
  calc
    injectiveMoment H raw9356 = injectiveMoment H raw9356step0 := by
      have heq : raw9356step0 = (fun i j => raw9356 (permutation396 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9356 permutation396 permutation10
    _ = injectiveMoment H node3315 := by rfl

def raw9357 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, -1, 1, 1], ![-1, 2, 2, -3]]

def raw9357step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 0, 0, 1], ![1, 1, -1, -1], ![1, -2, -2, 3]]

def raw9357step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical9357 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9357 = injectiveMoment H node3224 := by
  calc
    injectiveMoment H raw9357 = injectiveMoment H raw9357step0 := by
      have heq : raw9357step0 = -raw9357 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9357).symm
    injectiveMoment H raw9357step0 = injectiveMoment H raw9357step1 := by
      have heq : raw9357step1 = (fun i j => raw9357step0 (permutation373 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9357step0 permutation373 permutation15
    _ = injectiveMoment H node3224 := by rfl

def raw9358 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![0, 1, 3, -4]]

def raw9358step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical9358 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9358 = injectiveMoment H node3464 := by
  calc
    injectiveMoment H raw9358 = injectiveMoment H raw9358step0 := by
      have heq : raw9358step0 = (fun i j => raw9358 (permutation289 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9358 permutation289 permutation9
    _ = injectiveMoment H node3464 := by rfl

def raw9359 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![0, 0, -1, 1], ![-1, -1, 1, 1], ![0, 2, 2, -4]]

def raw9359step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical9359 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9359 = injectiveMoment H node3406 := by
  calc
    injectiveMoment H raw9359 = injectiveMoment H raw9359step0 := by
      have heq : raw9359step0 = (fun i j => raw9359 (permutation261 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9359 permutation261 permutation9
    _ = injectiveMoment H node3406 := by rfl

def raw9360 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw9360step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 1, -1], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw9360step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical9360 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9360 = injectiveMoment H node3120 := by
  calc
    injectiveMoment H raw9360 = injectiveMoment H raw9360step0 := by
      have heq : raw9360step0 = -raw9360 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9360).symm
    injectiveMoment H raw9360step0 = injectiveMoment H raw9360step1 := by
      have heq : raw9360step1 = (fun i j => raw9360step0 (permutation312 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9360step0 permutation312 permutation15
    _ = injectiveMoment H node3120 := by rfl

def raw9361 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 2, 0], ![0, 2, 1, -3]]

def raw9361step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 1, -1], ![2, 0, -2, 0], ![0, -2, -1, 3]]

def raw9361step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical9361 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9361 = injectiveMoment H node3136 := by
  calc
    injectiveMoment H raw9361 = injectiveMoment H raw9361step0 := by
      have heq : raw9361step0 = -raw9361 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9361).symm
    injectiveMoment H raw9361step0 = injectiveMoment H raw9361step1 := by
      have heq : raw9361step1 = (fun i j => raw9361step0 (permutation312 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9361step0 permutation312 permutation15
    _ = injectiveMoment H node3136 := by rfl

def raw9362 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw9362step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical9362 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9362 = injectiveMoment H node3292 := by
  calc
    injectiveMoment H raw9362 = injectiveMoment H raw9362step0 := by
      have heq : raw9362step0 = (fun i j => raw9362 (permutation263 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9362 permutation263 permutation9
    _ = injectiveMoment H node3292 := by rfl

def raw9363 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-1, 0, 2, -1], ![-1, 2, 1, -2]]

def raw9363step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 1, -1], ![1, 0, -2, 1], ![1, -2, -1, 2]]

def raw9363step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical9363 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9363 = injectiveMoment H node3266 := by
  calc
    injectiveMoment H raw9363 = injectiveMoment H raw9363step0 := by
      have heq : raw9363step0 = -raw9363 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9363).symm
    injectiveMoment H raw9363step0 = injectiveMoment H raw9363step1 := by
      have heq : raw9363step1 = (fun i j => raw9363step0 (permutation312 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9363step0 permutation312 permutation15
    _ = injectiveMoment H node3266 := by rfl

def raw9364 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-1, 1, 1, -1], ![-1, 1, 2, -2]]

def raw9364step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical9364 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9364 = injectiveMoment H node3462 := by
  calc
    injectiveMoment H raw9364 = injectiveMoment H raw9364step0 := by
      have heq : raw9364step0 = (fun i j => raw9364 (permutation395 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9364 permutation395 permutation10
    _ = injectiveMoment H node3462 := by rfl

def raw9365 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![0, 0, 2, -2], ![-2, 2, 1, -1]]

def raw9365step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical9365 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9365 = injectiveMoment H node3315 := by
  calc
    injectiveMoment H raw9365 = injectiveMoment H raw9365step0 := by
      have heq : raw9365step0 = (fun i j => raw9365 (permutation395 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9365 permutation395 permutation10
    _ = injectiveMoment H node3315 := by rfl

def raw9366 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 2, 2, -4]]

def raw9366step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -2, -2, 4]]

def raw9366step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9366 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9366 = injectiveMoment H node2880 := by
  calc
    injectiveMoment H raw9366 = injectiveMoment H raw9366step0 := by
      have heq : raw9366step0 = -raw9366 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9366).symm
    injectiveMoment H raw9366step0 = injectiveMoment H raw9366step1 := by
      have heq : raw9366step1 = (fun i j => raw9366step0 (permutation404 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9366step0 permutation404 permutation23
    _ = injectiveMoment H node2880 := by rfl

def raw9367 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![0, 2, 1, -3]]

def raw9367step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1], ![0, -2, -1, 3]]

def raw9367step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical9367 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9367 = injectiveMoment H node2979 := by
  calc
    injectiveMoment H raw9367 = injectiveMoment H raw9367step0 := by
      have heq : raw9367step0 = -raw9367 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9367).symm
    injectiveMoment H raw9367step0 = injectiveMoment H raw9367step1 := by
      have heq : raw9367step1 = (fun i j => raw9367step0 (permutation395 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9367step0 permutation395 permutation17
    _ = injectiveMoment H node2979 := by rfl

def raw9368 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![0, 2, 0, -2]]

def raw9368step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical9368 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9368 = injectiveMoment H node3157 := by
  calc
    injectiveMoment H raw9368 = injectiveMoment H raw9368step0 := by
      have heq : raw9368step0 = (fun i j => raw9368 (permutation294 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9368 permutation294 permutation13
    _ = injectiveMoment H node3157 := by rfl

def raw9369 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 1, 3, -4]]

def raw9369step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9369 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9369 = injectiveMoment H node3256 := by
  calc
    injectiveMoment H raw9369 = injectiveMoment H raw9369step0 := by
      have heq : raw9369step0 = (fun i j => raw9369 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9369 permutation262 permutation9
    _ = injectiveMoment H node3256 := by rfl

def raw9370 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, 1, 2, -3]]

def raw9370step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, -1, 0, -1], ![0, -1, -2, 3]]

def raw9370step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9370 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9370 = injectiveMoment H node2976 := by
  calc
    injectiveMoment H raw9370 = injectiveMoment H raw9370step0 := by
      have heq : raw9370step0 = -raw9370 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9370).symm
    injectiveMoment H raw9370step0 = injectiveMoment H raw9370step1 := by
      have heq : raw9370step1 = (fun i j => raw9370step0 (permutation404 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9370step0 permutation404 permutation23
    _ = injectiveMoment H node2976 := by rfl

def raw9371 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, 1, 0], ![-1, 2, 1, -2]]

def raw9371step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical9371 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9371 = injectiveMoment H node3046 := by
  calc
    injectiveMoment H raw9371 = injectiveMoment H raw9371step0 := by
      have heq : raw9371step0 = (fun i j => raw9371 (permutation404 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9371 permutation404 permutation28
    _ = injectiveMoment H node3046 := by rfl

def raw9372 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, 2, -1], ![-1, 2, 0, -1]]

def raw9372step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, -2, 1], ![1, -2, 0, 1]]

def raw9372step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9372 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9372 = injectiveMoment H node3193 := by
  calc
    injectiveMoment H raw9372 = injectiveMoment H raw9372step0 := by
      have heq : raw9372step0 = -raw9372 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9372).symm
    injectiveMoment H raw9372step0 = injectiveMoment H raw9372step1 := by
      have heq : raw9372step1 = (fun i j => raw9372step0 (permutation395 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9372step0 permutation395 permutation18
    _ = injectiveMoment H node3193 := by rfl

def raw9373 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, -1, 1], ![-1, 1, 3, -3]]

def raw9373step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9373 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9373 = injectiveMoment H node3461 := by
  calc
    injectiveMoment H raw9373 = injectiveMoment H raw9373step0 := by
      have heq : raw9373step0 = (fun i j => raw9373 (permutation395 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9373 permutation395 permutation10
    _ = injectiveMoment H node3461 := by rfl

def raw9374 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, 0, 0], ![-1, 1, 2, -2]]

def raw9374step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9374 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9374 = injectiveMoment H node3043 := by
  calc
    injectiveMoment H raw9374 = injectiveMoment H raw9374step0 := by
      have heq : raw9374step0 = (fun i j => raw9374 (permutation404 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9374 permutation404 permutation27
    _ = injectiveMoment H node3043 := by rfl

def raw9375 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, 1, -1], ![-1, 1, 1, -1]]

def raw9375step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9375 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9375 = injectiveMoment H node3398 := by
  calc
    injectiveMoment H raw9375 = injectiveMoment H raw9375step0 := by
      have heq : raw9375step0 = (fun i j => raw9375 (permutation294 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9375 permutation294 permutation14
    _ = injectiveMoment H node3398 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
