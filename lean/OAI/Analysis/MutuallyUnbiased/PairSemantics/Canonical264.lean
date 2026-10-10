import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8448 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, -1, 1], ![-1, -1, 1, 1], ![2, 0, 2, -4]]

def raw8448step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -1, 1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1], ![-2, 0, -2, 4]]

def raw8448step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical8448 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8448 = injectiveMoment H node3111 := by
  calc
    injectiveMoment H raw8448 = injectiveMoment H raw8448step0 := by
      have heq : raw8448step0 = -raw8448 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8448).symm
    injectiveMoment H raw8448step0 = injectiveMoment H raw8448step1 := by
      have heq : raw8448step1 = (fun i j => raw8448step0 (permutation357 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8448step0 permutation357 permutation9
    _ = injectiveMoment H node3111 := by rfl

def raw8449 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, -1, 1], ![-2, 0, 1, 1], ![2, 0, 2, -4]]

def raw8449step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical8449 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8449 = injectiveMoment H node3428 := by
  calc
    injectiveMoment H raw8449 = injectiveMoment H raw8449step0 := by
      have heq : raw8449step0 = (fun i j => raw8449 (permutation184 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8449 permutation184 permutation15
    _ = injectiveMoment H node3428 := by rfl

def raw8450 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 1, 2], ![2, 0, 2, -4]]

def raw8450step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

theorem canonical8450 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8450 = injectiveMoment H node3019 := by
  calc
    injectiveMoment H raw8450 = injectiveMoment H raw8450step0 := by
      have heq : raw8450step0 = (fun i j => raw8450 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8450 permutation258 permutation9
    _ = injectiveMoment H node3019 := by rfl

def raw8451 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, -1, 2, -3]]

def raw8451step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

theorem canonical8451 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8451 = injectiveMoment H node3201 := by
  calc
    injectiveMoment H raw8451 = injectiveMoment H raw8451step0 := by
      have heq : raw8451step0 = (fun i j => raw8451 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8451 permutation258 permutation9
    _ = injectiveMoment H node3201 := by rfl

def raw8452 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-1, -1, 1, 1], ![1, 0, 2, -3]]

def raw8452step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical8452 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8452 = injectiveMoment H node3402 := by
  calc
    injectiveMoment H raw8452 = injectiveMoment H raw8452step0 := by
      have heq : raw8452step0 = (fun i j => raw8452 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8452 permutation258 permutation9
    _ = injectiveMoment H node3402 := by rfl

def raw8453 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw8453step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

theorem canonical8453 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8453 = injectiveMoment H node3202 := by
  calc
    injectiveMoment H raw8453 = injectiveMoment H raw8453step0 := by
      have heq : raw8453step0 = (fun i j => raw8453 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8453 permutation258 permutation9
    _ = injectiveMoment H node3202 := by rfl

def raw8454 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw8454step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

theorem canonical8454 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8454 = injectiveMoment H node3274 := by
  calc
    injectiveMoment H raw8454 = injectiveMoment H raw8454step0 := by
      have heq : raw8454step0 = (fun i j => raw8454 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8454 permutation258 permutation9
    _ = injectiveMoment H node3274 := by rfl

def raw8455 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![1, 1, 2, -4]]

def raw8455step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem canonical8455 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8455 = injectiveMoment H node3021 := by
  calc
    injectiveMoment H raw8455 = injectiveMoment H raw8455step0 := by
      have heq : raw8455step0 = (fun i j => raw8455 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8455 permutation258 permutation9
    _ = injectiveMoment H node3021 := by rfl

def raw8456 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw8456step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem canonical8456 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8456 = injectiveMoment H node3424 := by
  calc
    injectiveMoment H raw8456 = injectiveMoment H raw8456step0 := by
      have heq : raw8456step0 = (fun i j => raw8456 (permutation184 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8456 permutation184 permutation15
    _ = injectiveMoment H node3424 := by rfl

def raw8457 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 0, 2, -3]]

def raw8457step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical8457 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8457 = injectiveMoment H node3430 := by
  calc
    injectiveMoment H raw8457 = injectiveMoment H raw8457step0 := by
      have heq : raw8457step0 = (fun i j => raw8457 (permutation184 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8457 permutation184 permutation15
    _ = injectiveMoment H node3430 := by rfl

def raw8458 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, -1, 3, -3]]

def raw8458step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

theorem canonical8458 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8458 = injectiveMoment H node3275 := by
  calc
    injectiveMoment H raw8458 = injectiveMoment H raw8458step0 := by
      have heq : raw8458step0 = (fun i j => raw8458 (permutation259 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8458 permutation259 permutation9
    _ = injectiveMoment H node3275 := by rfl

def raw8459 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -2, 0], ![0, -1, 3, -2]]

def raw8459step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![-1, 3, -2]]

def raw8459step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8459 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8459 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw8459 = injectiveMoment H raw8459step0 := by
      have hz : ∀ i, raw8459 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8459step0 = (fun i j => raw8459 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8459 permutation9 hz
    injectiveMoment H raw8459step0 = injectiveMoment H raw8459step1 := by
      have heq : raw8459step1 = (fun i j => raw8459step0 (permutation31 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8459step0 permutation31 permutation7
    _ = injectiveMoment H node185 := by rfl

def raw8460 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![0, -1, 0, 1]]

def raw8460step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -2, -1, 3], ![0, 1, 0, -1]]

def raw8460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![-2, -1, 3], ![1, 0, -1]]

def raw8460step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8460 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8460 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw8460 = injectiveMoment H raw8460step0 := by
      have heq : raw8460step0 = -raw8460 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8460).symm
    injectiveMoment H raw8460step0 = injectiveMoment H raw8460step1 := by
      have hz : ∀ i, raw8460step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8460step1 = (fun i j => raw8460step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8460step0 permutation9 hz
    injectiveMoment H raw8460step1 = injectiveMoment H raw8460step2 := by
      have heq : raw8460step2 = (fun i j => raw8460step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8460step1 permutation22 permutation5
    _ = injectiveMoment H node271 := by rfl

def raw8461 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![0, -1, -1, 2]]

def raw8461step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![0, -2, -2, 4], ![0, 1, 1, -2]]

def raw8461step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![-2, -2, 4], ![1, 1, -2]]

def raw8461step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical8461 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8461 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw8461 = injectiveMoment H raw8461step0 := by
      have heq : raw8461step0 = -raw8461 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8461).symm
    injectiveMoment H raw8461step0 = injectiveMoment H raw8461step1 := by
      have hz : ∀ i, raw8461step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8461step1 = (fun i j => raw8461step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8461step0 permutation9 hz
    injectiveMoment H raw8461step1 = injectiveMoment H raw8461step2 := by
      have heq : raw8461step2 = (fun i j => raw8461step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8461step1 permutation23 permutation3
    _ = injectiveMoment H node150 := by rfl

def raw8462 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw8462step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw8462step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical8462 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8462 = injectiveMoment H node3114 := by
  calc
    injectiveMoment H raw8462 = injectiveMoment H raw8462step0 := by
      have heq : raw8462step0 = -raw8462 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8462).symm
    injectiveMoment H raw8462step0 = injectiveMoment H raw8462step1 := by
      have heq : raw8462step1 = (fun i j => raw8462step0 (permutation382 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8462step0 permutation382 permutation15
    _ = injectiveMoment H node3114 := by rfl

def raw8463 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw8463step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical8463 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8463 = injectiveMoment H node3276 := by
  calc
    injectiveMoment H raw8463 = injectiveMoment H raw8463step0 := by
      have heq : raw8463step0 = (fun i j => raw8463 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8463 permutation262 permutation9
    _ = injectiveMoment H node3276 := by rfl

def raw8464 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, -1, -1, 1], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw8464step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 1, 1, -1], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw8464step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical8464 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8464 = injectiveMoment H node3114 := by
  calc
    injectiveMoment H raw8464 = injectiveMoment H raw8464step0 := by
      have heq : raw8464step0 = -raw8464 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8464).symm
    injectiveMoment H raw8464step0 = injectiveMoment H raw8464step1 := by
      have heq : raw8464step1 = (fun i j => raw8464step0 (permutation362 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8464step0 permutation362 permutation15
    _ = injectiveMoment H node3114 := by rfl

def raw8465 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, -1, -1, 1], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw8465step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical8465 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8465 = injectiveMoment H node3276 := by
  calc
    injectiveMoment H raw8465 = injectiveMoment H raw8465step0 := by
      have heq : raw8465step0 = (fun i j => raw8465 (permutation263 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8465 permutation263 permutation9
    _ = injectiveMoment H node3276 := by rfl

def raw8466 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 2, 2, -4]]

def raw8466step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical8466 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8466 = injectiveMoment H node3029 := by
  calc
    injectiveMoment H raw8466 = injectiveMoment H raw8466step0 := by
      have heq : raw8466step0 = (fun i j => raw8466 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8466 permutation262 permutation9
    _ = injectiveMoment H node3029 := by rfl

def raw8467 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw8467step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -1, -3, 4]]

def raw8467step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical8467 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8467 = injectiveMoment H node3412 := by
  calc
    injectiveMoment H raw8467 = injectiveMoment H raw8467step0 := by
      have heq : raw8467step0 = -raw8467 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8467).symm
    injectiveMoment H raw8467step0 = injectiveMoment H raw8467step1 := by
      have heq : raw8467step1 = (fun i j => raw8467step0 (permutation365 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8467step0 permutation365 permutation15
    _ = injectiveMoment H node3412 := by rfl

def raw8468 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 1, 2, -3]]

def raw8468step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -1, -2, 3]]

def raw8468step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical8468 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8468 = injectiveMoment H node3415 := by
  calc
    injectiveMoment H raw8468 = injectiveMoment H raw8468step0 := by
      have heq : raw8468step0 = -raw8468 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8468).symm
    injectiveMoment H raw8468step0 = injectiveMoment H raw8468step1 := by
      have heq : raw8468step1 = (fun i j => raw8468step0 (permutation365 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8468step0 permutation365 permutation15
    _ = injectiveMoment H node3415 := by rfl

def raw8469 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 0, 3, -3]]

def raw8469step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1]]

theorem canonical8469 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8469 = injectiveMoment H node3451 := by
  calc
    injectiveMoment H raw8469 = injectiveMoment H raw8469step0 := by
      have heq : raw8469step0 = (fun i j => raw8469 (permutation165 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8469 permutation165 permutation15
    _ = injectiveMoment H node3451 := by rfl

def raw8470 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8470step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical8470 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8470 = injectiveMoment H node2814 := by
  calc
    injectiveMoment H raw8470 = injectiveMoment H raw8470step0 := by
      have heq : raw8470step0 = (fun i j => raw8470 (permutation80 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8470 permutation80 permutation9
    _ = injectiveMoment H node2814 := by rfl

def raw8471 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-1, 1, -1, 1], ![1, 0, 0, -1]]

def raw8471step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical8471 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8471 = injectiveMoment H node1118 := by
  calc
    injectiveMoment H raw8471 = injectiveMoment H raw8471step0 := by
      have heq : raw8471step0 = (fun i j => raw8471 (permutation21 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8471 permutation21 permutation11
    _ = injectiveMoment H node1118 := by rfl

def raw8472 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8472step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem canonical8472 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8472 = injectiveMoment H node2857 := by
  calc
    injectiveMoment H raw8472 = injectiveMoment H raw8472step0 := by
      have heq : raw8472step0 = (fun i j => raw8472 (permutation80 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8472 permutation80 permutation9
    _ = injectiveMoment H node2857 := by rfl

def raw8473 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-1, 2, -3, 2], ![1, -1, 2, -2]]

def raw8473step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 1, -3, 2], ![1, -1, 2, -2]]

def raw8473step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![0, -1, 3, -2], ![-1, 1, -2, 2]]

def raw8473step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem canonical8473 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8473 = injectiveMoment H node1216 := by
  calc
    injectiveMoment H raw8473 = injectiveMoment H raw8473step0 := by
      have heq : raw8473step0 = raw8473.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8473).symm
    injectiveMoment H raw8473step0 = injectiveMoment H raw8473step1 := by
      have heq : raw8473step1 = -raw8473step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8473step0).symm
    injectiveMoment H raw8473step1 = injectiveMoment H raw8473step2 := by
      have heq : raw8473step2 = (fun i j => raw8473step1 (permutation21 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8473step1 permutation21 permutation16
    _ = injectiveMoment H node1216 := by rfl

def raw8474 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -1, -2, 2]]

def raw8474step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw8474step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 2, -2]]

theorem canonical8474 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8474 = injectiveMoment H node1261 := by
  calc
    injectiveMoment H raw8474 = injectiveMoment H raw8474step0 := by
      have heq : raw8474step0 = raw8474.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8474).symm
    injectiveMoment H raw8474step0 = injectiveMoment H raw8474step1 := by
      have heq : raw8474step1 = (fun i j => raw8474step0 (permutation15 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8474step0 permutation15 permutation10
    _ = injectiveMoment H node1261 := by rfl

def raw8475 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![-1, 2, 2, -3], ![1, -1, -3, 3]]

def raw8475step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def raw8475step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![0, -1, -2, 3], ![-1, 1, 3, -3]]

def raw8475step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 3, -3]]

theorem canonical8475 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8475 = injectiveMoment H node1218 := by
  calc
    injectiveMoment H raw8475 = injectiveMoment H raw8475step0 := by
      have heq : raw8475step0 = raw8475.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8475).symm
    injectiveMoment H raw8475step0 = injectiveMoment H raw8475step1 := by
      have heq : raw8475step1 = -raw8475step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8475step0).symm
    injectiveMoment H raw8475step1 = injectiveMoment H raw8475step2 := by
      have heq : raw8475step2 = (fun i j => raw8475step1 (permutation21 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8475step1 permutation21 permutation15
    _ = injectiveMoment H node1218 := by rfl

def raw8476 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, -1, -2, 2]]

def raw8476step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -1, 2]]

theorem canonical8476 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8476 = injectiveMoment H node2831 := by
  calc
    injectiveMoment H raw8476 = injectiveMoment H raw8476step0 := by
      have heq : raw8476step0 = (fun i j => raw8476 (permutation104 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8476 permutation104 permutation11
    _ = injectiveMoment H node2831 := by rfl

def raw8477 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, -2, 3]]

def raw8477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![-1, -2, 3]]

def raw8477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8477 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8477 = injectiveMoment H node562 := by
  calc
    injectiveMoment H raw8477 = injectiveMoment H raw8477step0 := by
      have hz : ∀ i, raw8477 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8477step0 = (fun i j => raw8477 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8477 permutation9 hz
    injectiveMoment H raw8477step0 = injectiveMoment H raw8477step1 := by
      have heq : raw8477step1 = (fun i j => raw8477step0 (permutation132 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8477step0 permutation132 permutation5
    _ = injectiveMoment H node562 := by rfl

def raw8478 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 0, 0]]

def raw8478step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0]]

def raw8478step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical8478 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8478 = injectiveMoment H node64 := by
  calc
    injectiveMoment H raw8478 = injectiveMoment H raw8478step0 := by
      have hz : ∀ j, raw8478 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw8478step0 = (fun i j => raw8478 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8478 permutation27 hz
    injectiveMoment H raw8478step0 = injectiveMoment H raw8478step1 := by
      have hz : ∀ i, raw8478step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8478step1 = (fun i j => raw8478step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8478step0 permutation9 hz
    _ = injectiveMoment H node64 := by rfl

def raw8479 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 1, -1], ![1, -1, -2, 2]]

def raw8479step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem canonical8479 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8479 = injectiveMoment H node2857 := by
  calc
    injectiveMoment H raw8479 = injectiveMoment H raw8479step0 := by
      have heq : raw8479step0 = (fun i j => raw8479 (permutation104 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8479 permutation104 permutation9
    _ = injectiveMoment H node2857 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
