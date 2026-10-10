import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes54

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9312 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, 3, -3], ![1, -2, 0, 1]]

def raw9312step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

theorem canonical9312 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9312 = injectiveMoment H node2836 := by
  calc
    injectiveMoment H raw9312 = injectiveMoment H raw9312step0 := by
      have heq : raw9312step0 = (fun i j => raw9312 (permutation104 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9312 permutation104 permutation10
    _ = injectiveMoment H node2836 := by rfl

def raw9313 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, -1, 0, 1], ![-1, -1, 1, 1], ![1, 1, 2, -4]]

def raw9313step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 1, -1, -1], ![-1, -1, -2, 4]]

def raw9313step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical9313 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9313 = injectiveMoment H node3347 := by
  calc
    injectiveMoment H raw9313 = injectiveMoment H raw9313step0 := by
      have heq : raw9313step0 = -raw9313 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9313).symm
    injectiveMoment H raw9313step0 = injectiveMoment H raw9313step1 := by
      have heq : raw9313step1 = (fun i j => raw9313step0 (permutation355 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9313step0 permutation355 permutation9
    _ = injectiveMoment H node3347 := by rfl

def raw9314 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, 3, -1]]

def raw9314step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical9314 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9314 = injectiveMoment H node2966 := by
  calc
    injectiveMoment H raw9314 = injectiveMoment H raw9314step0 := by
      have heq : raw9314step0 = (fun i j => raw9314 (permutation383 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9314 permutation383 permutation13
    _ = injectiveMoment H node2966 := by rfl

def raw9315 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![0, -2, 1, 1]]

def raw9315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![-2, 1, 1]]

def raw9315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical9315 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9315 = injectiveMoment H node708 := by
  calc
    injectiveMoment H raw9315 = injectiveMoment H raw9315step0 := by
      have hz : ∀ i, raw9315 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9315step0 = (fun i j => raw9315 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9315 permutation9 hz
    injectiveMoment H raw9315step0 = injectiveMoment H raw9315step1 := by
      have heq : raw9315step1 = (fun i j => raw9315step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9315step0 permutation128 permutation3
    _ = injectiveMoment H node708 := by rfl

def raw9316 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![0, -2, 0, 2]]

def raw9316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4], ![-2, 0, 2]]

def raw9316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical9316 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9316 = injectiveMoment H node653 := by
  calc
    injectiveMoment H raw9316 = injectiveMoment H raw9316step0 := by
      have hz : ∀ i, raw9316 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9316step0 = (fun i j => raw9316 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9316 permutation9 hz
    injectiveMoment H raw9316step0 = injectiveMoment H raw9316step1 := by
      have heq : raw9316step1 = (fun i j => raw9316step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9316step0 permutation128 permutation3
    _ = injectiveMoment H node653 := by rfl

def raw9317 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw9317step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 2, -4]]

theorem canonical9317 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9317 = injectiveMoment H node3213 := by
  calc
    injectiveMoment H raw9317 = injectiveMoment H raw9317step0 := by
      have heq : raw9317step0 = (fun i j => raw9317 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9317 permutation258 permutation9
    _ = injectiveMoment H node3213 := by rfl

def raw9318 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw9318step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

theorem canonical9318 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9318 = injectiveMoment H node3290 := by
  calc
    injectiveMoment H raw9318 = injectiveMoment H raw9318step0 := by
      have heq : raw9318step0 = (fun i j => raw9318 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9318 permutation258 permutation9
    _ = injectiveMoment H node3290 := by rfl

def raw9319 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 0, -1], ![-2, 1, 3, -2]]

def raw9319step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

theorem canonical9319 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9319 = injectiveMoment H node3243 := by
  calc
    injectiveMoment H raw9319 = injectiveMoment H raw9319step0 := by
      have heq : raw9319step0 = (fun i j => raw9319 (permutation308 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9319 permutation308 permutation10
    _ = injectiveMoment H node3243 := by rfl

def raw9320 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 1, 2], ![1, 1, 2, -4]]

def raw9320step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem canonical9320 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9320 = injectiveMoment H node3052 := by
  calc
    injectiveMoment H raw9320 = injectiveMoment H raw9320step0 := by
      have heq : raw9320step0 = (fun i j => raw9320 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9320 permutation258 permutation9
    _ = injectiveMoment H node3052 := by rfl

def raw9321 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw9321step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![-1, 0, -3, 4]]

def raw9321step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem canonical9321 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9321 = injectiveMoment H node3456 := by
  calc
    injectiveMoment H raw9321 = injectiveMoment H raw9321step0 := by
      have heq : raw9321step0 = -raw9321 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9321).symm
    injectiveMoment H raw9321step0 = injectiveMoment H raw9321step1 := by
      have heq : raw9321step1 = (fun i j => raw9321step0 (permutation236 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9321step0 permutation236 permutation15
    _ = injectiveMoment H node3456 := by rfl

def raw9322 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![1, 0, 2, -3]]

def raw9322step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![2, 0, -1, -1], ![-1, 0, -2, 3]]

def raw9322step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

theorem canonical9322 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9322 = injectiveMoment H node3447 := by
  calc
    injectiveMoment H raw9322 = injectiveMoment H raw9322step0 := by
      have heq : raw9322step0 = -raw9322 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9322).symm
    injectiveMoment H raw9322step0 = injectiveMoment H raw9322step1 := by
      have heq : raw9322step1 = (fun i j => raw9322step0 (permutation236 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9322step0 permutation236 permutation16
    _ = injectiveMoment H node3447 := by rfl

def raw9323 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, -1, 3, -3]]

def raw9323step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem canonical9323 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9323 = injectiveMoment H node3291 := by
  calc
    injectiveMoment H raw9323 = injectiveMoment H raw9323step0 := by
      have heq : raw9323step0 = (fun i j => raw9323 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9323 permutation258 permutation9
    _ = injectiveMoment H node3291 := by rfl

def raw9324 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, -1, 2, -2]]

def raw9324step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9324 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9324 = injectiveMoment H node3042 := by
  calc
    injectiveMoment H raw9324 = injectiveMoment H raw9324step0 := by
      have heq : raw9324step0 = (fun i j => raw9324 (permutation393 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9324 permutation393 permutation29
    _ = injectiveMoment H node3042 := by rfl

def raw9325 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 1, 1], ![0, 1, 2, -3]]

def raw9325step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical9325 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9325 = injectiveMoment H node3407 := by
  calc
    injectiveMoment H raw9325 = injectiveMoment H raw9325step0 := by
      have heq : raw9325step0 = (fun i j => raw9325 (permutation259 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9325 permutation259 permutation9
    _ = injectiveMoment H node3407 := by rfl

def raw9326 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 3, -2]]

def raw9326step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9326 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9326 = injectiveMoment H node2888 := by
  calc
    injectiveMoment H raw9326 = injectiveMoment H raw9326step0 := by
      have heq : raw9326step0 = (fun i j => raw9326 (permutation366 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9326 permutation366 permutation27
    _ = injectiveMoment H node2888 := by rfl

def raw9327 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 3, -1]]

def raw9327step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 0, -3, 1]]

def raw9327step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical9327 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9327 = injectiveMoment H node3440 := by
  calc
    injectiveMoment H raw9327 = injectiveMoment H raw9327step0 := by
      have heq : raw9327step0 = -raw9327 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9327).symm
    injectiveMoment H raw9327step0 = injectiveMoment H raw9327step1 := by
      have heq : raw9327step1 = (fun i j => raw9327step0 (permutation223 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9327step0 permutation223 permutation19
    _ = injectiveMoment H node3440 := by rfl

def raw9328 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![-2, 1, 1, 0], ![1, -2, 2, -1]]

def raw9328step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

theorem canonical9328 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9328 = injectiveMoment H node3045 := by
  calc
    injectiveMoment H raw9328 = injectiveMoment H raw9328step0 := by
      have heq : raw9328step0 = (fun i j => raw9328 (permutation374 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9328 permutation374 permutation19
    _ = injectiveMoment H node3045 := by rfl

def raw9329 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, -1, 2, -1]]

def raw9329step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1]]

def raw9329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical9329 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9329 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw9329 = injectiveMoment H raw9329step0 := by
      have hz : ∀ i, raw9329 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9329step0 = (fun i j => raw9329 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9329 permutation9 hz
    injectiveMoment H raw9329step0 = injectiveMoment H raw9329step1 := by
      have heq : raw9329step1 = (fun i j => raw9329step0 (permutation27 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9329step0 permutation27 permutation4
    _ = injectiveMoment H node287 := by rfl

def raw9330 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -2, 0, 0], ![-2, 0, 3, -1]]

def raw9330step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical9330 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9330 = injectiveMoment H node2966 := by
  calc
    injectiveMoment H raw9330 = injectiveMoment H raw9330step0 := by
      have heq : raw9330step0 = (fun i j => raw9330 (permutation363 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9330 permutation363 permutation13
    _ = injectiveMoment H node2966 := by rfl

def raw9331 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, -1, 1], ![-2, 0, 3, -1]]

def raw9331step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

theorem canonical9331 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9331 = injectiveMoment H node3135 := by
  calc
    injectiveMoment H raw9331 = injectiveMoment H raw9331step0 := by
      have heq : raw9331step0 = (fun i j => raw9331 (permutation308 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9331 permutation308 permutation10
    _ = injectiveMoment H node3135 := by rfl

def raw9332 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, 2, 0]]

def raw9332step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical9332 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9332 = injectiveMoment H node3168 := by
  calc
    injectiveMoment H raw9332 = injectiveMoment H raw9332step0 := by
      have heq : raw9332step0 = (fun i j => raw9332 (permutation363 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9332 permutation363 permutation13
    _ = injectiveMoment H node3168 := by rfl

def raw9333 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 0, 1], ![1, 0, 0, -1], ![-2, 1, 2, -1]]

def raw9333step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 2, 0, -1], ![-1, 0, 0, 1], ![2, -1, -2, 1]]

def raw9333step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9333 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9333 = injectiveMoment H node3094 := by
  calc
    injectiveMoment H raw9333 = injectiveMoment H raw9333step0 := by
      have heq : raw9333step0 = -raw9333 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9333).symm
    injectiveMoment H raw9333step0 = injectiveMoment H raw9333step1 := by
      have heq : raw9333step1 = (fun i j => raw9333step0 (permutation371 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9333step0 permutation371 permutation23
    _ = injectiveMoment H node3094 := by rfl

def raw9334 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![-2, 1, 1, 0], ![1, -1, 2, -2]]

def raw9334step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 1, -1]]

theorem canonical9334 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9334 = injectiveMoment H node3295 := by
  calc
    injectiveMoment H raw9334 = injectiveMoment H raw9334step0 := by
      have heq : raw9334step0 = (fun i j => raw9334 (permutation259 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9334 permutation259 permutation10
    _ = injectiveMoment H node3295 := by rfl

def raw9335 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 1, 3, -2]]

def raw9335step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical9335 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9335 = injectiveMoment H node3242 := by
  calc
    injectiveMoment H raw9335 = injectiveMoment H raw9335step0 := by
      have heq : raw9335step0 = (fun i j => raw9335 (permutation309 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9335 permutation309 permutation10
    _ = injectiveMoment H node3242 := by rfl

def raw9336 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, -1, 2, -2]]

def raw9336step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, -1, 0, -1], ![-1, 1, -2, 2]]

def raw9336step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9336 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9336 = injectiveMoment H node3040 := by
  calc
    injectiveMoment H raw9336 = injectiveMoment H raw9336step0 := by
      have heq : raw9336step0 = -raw9336 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9336).symm
    injectiveMoment H raw9336step0 = injectiveMoment H raw9336step1 := by
      have heq : raw9336step1 = (fun i j => raw9336step0 (permutation387 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9336step0 permutation387 permutation21
    _ = injectiveMoment H node3040 := by rfl

def raw9337 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, -1, 1, -1]]

def raw9337step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical9337 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9337 = injectiveMoment H node3208 := by
  calc
    injectiveMoment H raw9337 = injectiveMoment H raw9337step0 := by
      have heq : raw9337step0 = (fun i j => raw9337 (permutation284 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9337 permutation284 permutation14
    _ = injectiveMoment H node3208 := by rfl

def raw9338 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 1, 3, -2]]

def raw9338step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical9338 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9338 = injectiveMoment H node3242 := by
  calc
    injectiveMoment H raw9338 = injectiveMoment H raw9338step0 := by
      have heq : raw9338step0 = (fun i j => raw9338 (permutation308 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9338 permutation308 permutation10
    _ = injectiveMoment H node3242 := by rfl

def raw9339 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 2, -1]]

def raw9339step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical9339 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9339 = injectiveMoment H node3046 := by
  calc
    injectiveMoment H raw9339 = injectiveMoment H raw9339step0 := by
      have heq : raw9339step0 = (fun i j => raw9339 (permutation355 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9339 permutation355 permutation13
    _ = injectiveMoment H node3046 := by rfl

def raw9340 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 2, 0]]

def raw9340step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 0, -2, 0]]

def raw9340step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical9340 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9340 = injectiveMoment H node3437 := by
  calc
    injectiveMoment H raw9340 = injectiveMoment H raw9340step0 := by
      have heq : raw9340step0 = -raw9340 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9340).symm
    injectiveMoment H raw9340step0 = injectiveMoment H raw9340step1 := by
      have heq : raw9340step1 = (fun i j => raw9340step0 (permutation240 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9340step0 permutation240 permutation17
    _ = injectiveMoment H node3437 := by rfl

def raw9341 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![1, -2, 2, -1]]

def raw9341step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem canonical9341 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9341 = injectiveMoment H node3086 := by
  calc
    injectiveMoment H raw9341 = injectiveMoment H raw9341step0 := by
      have heq : raw9341step0 = (fun i j => raw9341 (permutation373 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9341 permutation373 permutation19
    _ = injectiveMoment H node3086 := by rfl

def raw9342 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 0, 0, 2], ![1, -1, 2, -2]]

def raw9342step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![2, 0, 0, -2], ![-1, 1, -2, 2]]

def raw9342step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical9342 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9342 = injectiveMoment H node3444 := by
  calc
    injectiveMoment H raw9342 = injectiveMoment H raw9342step0 := by
      have heq : raw9342step0 = -raw9342 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9342).symm
    injectiveMoment H raw9342step0 = injectiveMoment H raw9342step1 := by
      have heq : raw9342step1 = (fun i j => raw9342step0 (permutation228 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9342step0 permutation228 permutation15
    _ = injectiveMoment H node3444 := by rfl

def raw9343 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -2, 2, -1]]

def raw9343step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![2, -1, 0, -1], ![-1, 2, -2, 1]]

def raw9343step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9343 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9343 = injectiveMoment H node3094 := by
  calc
    injectiveMoment H raw9343 = injectiveMoment H raw9343step0 := by
      have heq : raw9343step0 = -raw9343 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9343).symm
    injectiveMoment H raw9343step0 = injectiveMoment H raw9343step1 := by
      have heq : raw9343step1 = (fun i j => raw9343step0 (permutation387 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9343step0 permutation387 permutation21
    _ = injectiveMoment H node3094 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
