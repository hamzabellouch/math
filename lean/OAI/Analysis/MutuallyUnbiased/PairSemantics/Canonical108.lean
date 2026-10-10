import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3456 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw3456step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![0, 0, 0, -1, 1], ![0, -1, 0, -1, 2], ![2, 1, 0, 1, -4]]

def raw3456step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, -1, -1], ![0, 0, 0, 1, -1], ![0, 1, 0, 1, -2], ![-2, -1, 0, -1, 4]]

def raw3456step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![-2, -1, -1, 4]]

def raw3456step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical3456 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3456 = injectiveMoment H node769 := by
  calc
    injectiveMoment H raw3456 = injectiveMoment H raw3456step0 := by
      have heq : raw3456step0 = raw3456.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3456).symm
    injectiveMoment H raw3456step0 = injectiveMoment H raw3456step1 := by
      have heq : raw3456step1 = -raw3456step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3456step0).symm
    injectiveMoment H raw3456step1 = injectiveMoment H raw3456step2 := by
      have hz : ∀ i, raw3456step1 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw3456step2 = (fun i j => raw3456step1 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw3456step1 permutation80 hz
    injectiveMoment H raw3456step2 = injectiveMoment H raw3456step3 := by
      have heq : raw3456step3 = (fun i j => raw3456step2 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3456step2 permutation29 permutation15
    _ = injectiveMoment H node769 := by rfl

def raw3457 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw3457step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![-1, -1, 1, 1]]

def raw3457step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical3457 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3457 = injectiveMoment H node2643 := by
  calc
    injectiveMoment H raw3457 = injectiveMoment H raw3457step0 := by
      have heq : raw3457step0 = -raw3457 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3457).symm
    injectiveMoment H raw3457step0 = injectiveMoment H raw3457step1 := by
      have heq : raw3457step1 = (fun i j => raw3457step0 (permutation141 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3457step0 permutation141 permutation15
    _ = injectiveMoment H node2643 := by rfl

def raw3458 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw3458step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, 0, -2, 2], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw3458step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem canonical3458 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3458 = injectiveMoment H node2635 := by
  calc
    injectiveMoment H raw3458 = injectiveMoment H raw3458step0 := by
      have heq : raw3458step0 = -raw3458 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3458).symm
    injectiveMoment H raw3458step0 = injectiveMoment H raw3458step1 := by
      have heq : raw3458step1 = (fun i j => raw3458step0 (permutation141 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3458step0 permutation141 permutation15
    _ = injectiveMoment H node2635 := by rfl

def raw3459 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

theorem canonical3459 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3459 = injectiveMoment H node2030 := by
  rfl

def raw3460 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem canonical3460 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3460 = injectiveMoment H node2031 := by
  rfl

def raw3461 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw3461step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 2, -1], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw3461step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

theorem canonical3461 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3461 = injectiveMoment H node2829 := by
  calc
    injectiveMoment H raw3461 = injectiveMoment H raw3461step0 := by
      have heq : raw3461step0 = -raw3461 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3461).symm
    injectiveMoment H raw3461step0 = injectiveMoment H raw3461step1 := by
      have heq : raw3461step1 = (fun i j => raw3461step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3461step0 permutation100 permutation15
    _ = injectiveMoment H node2829 := by rfl

def raw3462 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 0, 0], ![2, -1, 2, -3]]

def raw3462step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 1, 0, -1], ![0, -1, -1, 0, 2], ![2, 1, 0, 0, -3]]

def raw3462step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, -1, -1, 2], ![2, 1, 0, -3]]

def raw3462step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical3462 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3462 = injectiveMoment H node1032 := by
  calc
    injectiveMoment H raw3462 = injectiveMoment H raw3462step0 := by
      have heq : raw3462step0 = raw3462.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3462).symm
    injectiveMoment H raw3462step0 = injectiveMoment H raw3462step1 := by
      have hz : ∀ i, raw3462step0 i (permutation104 0) = 0 := by decide +kernel
      have heq : raw3462step1 = (fun i j => raw3462step0 i (permutation104 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw3462step0 permutation104 hz
    injectiveMoment H raw3462step1 = injectiveMoment H raw3462step2 := by
      have heq : raw3462step2 = (fun i j => raw3462step1 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3462step1 permutation21 permutation17
    _ = injectiveMoment H node1032 := by rfl

def raw3463 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 3, -3]]

theorem canonical3463 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3463 = injectiveMoment H node2032 := by
  rfl

def raw3464 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3464step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-2, 2, -2, 2]]

def raw3464step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical3464 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3464 = injectiveMoment H node1518 := by
  calc
    injectiveMoment H raw3464 = injectiveMoment H raw3464step0 := by
      have heq : raw3464step0 = -raw3464 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3464).symm
    injectiveMoment H raw3464step0 = injectiveMoment H raw3464step1 := by
      have heq : raw3464step1 = (fun i j => raw3464step0 (permutation150 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3464step0 permutation150 permutation11
    _ = injectiveMoment H node1518 := by rfl

def raw3465 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw3465step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, -2, 3], ![-2, 2, 0, 0]]

def raw3465step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical3465 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3465 = injectiveMoment H node1702 := by
  calc
    injectiveMoment H raw3465 = injectiveMoment H raw3465step0 := by
      have heq : raw3465step0 = -raw3465 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3465).symm
    injectiveMoment H raw3465step0 = injectiveMoment H raw3465step1 := by
      have heq : raw3465step1 = (fun i j => raw3465step0 (permutation109 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3465step0 permutation109 permutation23
    _ = injectiveMoment H node1702 := by rfl

def raw3466 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, -1, 1]]

theorem canonical3466 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3466 = injectiveMoment H node2033 := by
  rfl

def raw3467 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw3467step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 2, 0, -1], ![-1, -1, -2, 4]]

def raw3467step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical3467 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3467 = injectiveMoment H node1581 := by
  calc
    injectiveMoment H raw3467 = injectiveMoment H raw3467step0 := by
      have heq : raw3467step0 = -raw3467 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3467).symm
    injectiveMoment H raw3467step0 = injectiveMoment H raw3467step1 := by
      have heq : raw3467step1 = (fun i j => raw3467step0 (permutation146 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3467step0 permutation146 permutation21
    _ = injectiveMoment H node1581 := by rfl

def raw3468 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw3468step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![1, 1, -2, 0], ![1, 1, 1, -3]]

theorem canonical3468 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3468 = injectiveMoment H node2007 := by
  calc
    injectiveMoment H raw3468 = injectiveMoment H raw3468step0 := by
      have heq : raw3468step0 = (fun i j => raw3468 (permutation33 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3468 permutation33 permutation11
    _ = injectiveMoment H node2007 := by rfl

def raw3469 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw3469step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 1, -1], ![-1, 0, -3, 4]]

def raw3469step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical3469 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3469 = injectiveMoment H node2807 := by
  calc
    injectiveMoment H raw3469 = injectiveMoment H raw3469step0 := by
      have heq : raw3469step0 = -raw3469 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3469).symm
    injectiveMoment H raw3469step0 = injectiveMoment H raw3469step1 := by
      have heq : raw3469step1 = (fun i j => raw3469step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3469step0 permutation100 permutation15
    _ = injectiveMoment H node2807 := by rfl

def raw3470 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def raw3470step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![0, -1, -2, 3]]

def raw3470step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical3470 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3470 = injectiveMoment H node3017 := by
  calc
    injectiveMoment H raw3470 = injectiveMoment H raw3470step0 := by
      have heq : raw3470step0 = -raw3470 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3470).symm
    injectiveMoment H raw3470step0 = injectiveMoment H raw3470step1 := by
      have heq : raw3470step1 = (fun i j => raw3470step0 (permutation325 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3470step0 permutation325 permutation23
    _ = injectiveMoment H node3017 := by rfl

def raw3471 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw3471step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, -3, 3], ![-1, 0, 1, 0]]

def raw3471step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -2, 0], ![1, -1, 3, -3]]

theorem canonical3471 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3471 = injectiveMoment H node2754 := by
  calc
    injectiveMoment H raw3471 = injectiveMoment H raw3471step0 := by
      have heq : raw3471step0 = -raw3471 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3471).symm
    injectiveMoment H raw3471step0 = injectiveMoment H raw3471step1 := by
      have heq : raw3471step1 = (fun i j => raw3471step0 (permutation100 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3471step0 permutation100 permutation16
    _ = injectiveMoment H node2754 := by rfl

def raw3472 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def raw3472step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, -3, 3], ![-1, 0, 2, -1]]

def raw3472step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

theorem canonical3472 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3472 = injectiveMoment H node2776 := by
  calc
    injectiveMoment H raw3472 = injectiveMoment H raw3472step0 := by
      have heq : raw3472step0 = -raw3472 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3472).symm
    injectiveMoment H raw3472step0 = injectiveMoment H raw3472step1 := by
      have heq : raw3472step1 = (fun i j => raw3472step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3472step0 permutation100 permutation15
    _ = injectiveMoment H node2776 := by rfl

def raw3473 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3473step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, 1, -1], ![0, -1, -3, 4], ![-1, 1, 1, -1], ![-1, 0, 1, 0]]

def raw3473step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical3473 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3473 = injectiveMoment H node2686 := by
  calc
    injectiveMoment H raw3473 = injectiveMoment H raw3473step0 := by
      have heq : raw3473step0 = -raw3473 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3473).symm
    injectiveMoment H raw3473step0 = injectiveMoment H raw3473step1 := by
      have heq : raw3473step1 = (fun i j => raw3473step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3473step0 permutation100 permutation15
    _ = injectiveMoment H node2686 := by rfl

def raw3474 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 1, -2, 0]]

def raw3474step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, -1, 3, -2], ![2, 1, -3, 0]]

def raw3474step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, 1, -3, 2], ![-2, -1, 3, 0]]

def raw3474step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

theorem canonical3474 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3474 = injectiveMoment H node799 := by
  calc
    injectiveMoment H raw3474 = injectiveMoment H raw3474step0 := by
      have heq : raw3474step0 = raw3474.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3474).symm
    injectiveMoment H raw3474step0 = injectiveMoment H raw3474step1 := by
      have heq : raw3474step1 = -raw3474step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3474step0).symm
    injectiveMoment H raw3474step1 = injectiveMoment H raw3474step2 := by
      have heq : raw3474step2 = (fun i j => raw3474step1 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3474step1 permutation29 permutation16
    _ = injectiveMoment H node799 := by rfl

def raw3475 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 0, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3475step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 1, 1, -2], ![0, 0, -2, 0, 2], ![2, 0, 1, -1, -2]]

def raw3475step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![0, 0, -1, -1, 2], ![0, 0, 2, 0, -2], ![-2, 0, -1, 1, 2]]

def raw3475step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def raw3475step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical3475 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3475 = injectiveMoment H node1059 := by
  calc
    injectiveMoment H raw3475 = injectiveMoment H raw3475step0 := by
      have heq : raw3475step0 = raw3475.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3475).symm
    injectiveMoment H raw3475step0 = injectiveMoment H raw3475step1 := by
      have heq : raw3475step1 = -raw3475step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3475step0).symm
    injectiveMoment H raw3475step1 = injectiveMoment H raw3475step2 := by
      have hz : ∀ i, raw3475step1 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw3475step2 = (fun i j => raw3475step1 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw3475step1 permutation57 hz
    injectiveMoment H raw3475step2 = injectiveMoment H raw3475step3 := by
      have heq : raw3475step3 = (fun i j => raw3475step2 (permutation15 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3475step2 permutation15 permutation23
    _ = injectiveMoment H node1059 := by rfl

def raw3476 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3476step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![0, 0, 1, 1, -2], ![0, 0, -1, -1, 2], ![2, 0, 0, 0, -2]]

def raw3476step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -1, -1, 2], ![2, 0, 0, -2]]

def raw3476step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem canonical3476 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3476 = injectiveMoment H node1027 := by
  calc
    injectiveMoment H raw3476 = injectiveMoment H raw3476step0 := by
      have heq : raw3476step0 = raw3476.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3476).symm
    injectiveMoment H raw3476step0 = injectiveMoment H raw3476step1 := by
      have hz : ∀ i, raw3476step0 i (permutation57 0) = 0 := by decide +kernel
      have heq : raw3476step1 = (fun i j => raw3476step0 i (permutation57 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw3476step0 permutation57 hz
    injectiveMoment H raw3476step1 = injectiveMoment H raw3476step2 := by
      have heq : raw3476step2 = (fun i j => raw3476step1 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3476step1 permutation22 permutation17
    _ = injectiveMoment H node1027 := by rfl

def raw3477 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 0, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def raw3477step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![2, 0, 1, -3]]

def raw3477step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-2, 0, -1, 3]]

def raw3477step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -1, 3]]

def raw3477step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical3477 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3477 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw3477 = injectiveMoment H raw3477step0 := by
      have heq : raw3477step0 = raw3477.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3477).symm
    injectiveMoment H raw3477step0 = injectiveMoment H raw3477step1 := by
      have heq : raw3477step1 = -raw3477step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3477step0).symm
    injectiveMoment H raw3477step1 = injectiveMoment H raw3477step2 := by
      have hz : ∀ i, raw3477step1 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw3477step2 = (fun i j => raw3477step1 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw3477step1 permutation15 hz
    injectiveMoment H raw3477step2 = injectiveMoment H raw3477step3 := by
      have heq : raw3477step3 = (fun i j => raw3477step2 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3477step2 permutation30 permutation3
    _ = injectiveMoment H node176 := by rfl

def raw3478 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 0, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw3478step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![2, 0, -1, -1]]

def raw3478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical3478 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3478 = injectiveMoment H node227 := by
  calc
    injectiveMoment H raw3478 = injectiveMoment H raw3478step0 := by
      have heq : raw3478step0 = raw3478.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3478).symm
    injectiveMoment H raw3478step0 = injectiveMoment H raw3478step1 := by
      have hz : ∀ i, raw3478step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw3478step1 = (fun i j => raw3478step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw3478step0 permutation15 hz
    _ = injectiveMoment H node227 := by rfl

def raw3479 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3479step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3479step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical3479 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3479 = injectiveMoment H node1054 := by
  calc
    injectiveMoment H raw3479 = injectiveMoment H raw3479step0 := by
      have hz : ∀ j, raw3479 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw3479step0 = (fun i j => raw3479 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw3479 permutation80 hz
    injectiveMoment H raw3479step0 = injectiveMoment H raw3479step1 := by
      have heq : raw3479step1 = (fun i j => raw3479step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3479step0 permutation27 permutation18
    _ = injectiveMoment H node1054 := by rfl

def raw3480 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3480step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3480step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical3480 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3480 = injectiveMoment H node2609 := by
  calc
    injectiveMoment H raw3480 = injectiveMoment H raw3480step0 := by
      have heq : raw3480step0 = -raw3480 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3480).symm
    injectiveMoment H raw3480step0 = injectiveMoment H raw3480step1 := by
      have heq : raw3480step1 = (fun i j => raw3480step0 (permutation135 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3480step0 permutation135 permutation16
    _ = injectiveMoment H node2609 := by rfl

def raw3481 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem canonical3481 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3481 = injectiveMoment H node2034 := by
  rfl

def raw3482 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

theorem canonical3482 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3482 = injectiveMoment H node2035 := by
  rfl

def raw3483 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3483step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -1, 1], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-2, 2, -1, 1]]

def raw3483step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical3483 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3483 = injectiveMoment H node1839 := by
  calc
    injectiveMoment H raw3483 = injectiveMoment H raw3483step0 := by
      have heq : raw3483step0 = -raw3483 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3483).symm
    injectiveMoment H raw3483step0 = injectiveMoment H raw3483step1 := by
      have heq : raw3483step1 = (fun i j => raw3483step0 (permutation138 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3483step0 permutation138 permutation11
    _ = injectiveMoment H node1839 := by rfl

def raw3484 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![2, -1, -1, 0]]

def raw3484step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical3484 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3484 = injectiveMoment H node2613 := by
  calc
    injectiveMoment H raw3484 = injectiveMoment H raw3484step0 := by
      have heq : raw3484step0 = (fun i j => raw3484 (permutation129 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3484 permutation129 permutation18
    _ = injectiveMoment H node2613 := by rfl

def raw3485 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def raw3485step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

theorem canonical3485 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3485 = injectiveMoment H node2035 := by
  calc
    injectiveMoment H raw3485 = injectiveMoment H raw3485step0 := by
      have heq : raw3485step0 = (fun i j => raw3485 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3485 permutation35 permutation9
    _ = injectiveMoment H node2035 := by rfl

def raw3486 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3486step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical3486 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3486 = injectiveMoment H node3169 := by
  calc
    injectiveMoment H raw3486 = injectiveMoment H raw3486step0 := by
      have heq : raw3486step0 = (fun i j => raw3486 (permutation169 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3486 permutation169 permutation11
    _ = injectiveMoment H node3169 := by rfl

def raw3487 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw3487step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -1, 1], ![0, -1, 1, 0], ![0, -1, 1, 0], ![-2, 2, -1, 1]]

def raw3487step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical3487 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3487 = injectiveMoment H node1749 := by
  calc
    injectiveMoment H raw3487 = injectiveMoment H raw3487step0 := by
      have heq : raw3487step0 = -raw3487 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3487).symm
    injectiveMoment H raw3487step0 = injectiveMoment H raw3487step1 := by
      have heq : raw3487step1 = (fun i j => raw3487step0 (permutation136 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3487step0 permutation136 permutation12
    _ = injectiveMoment H node1749 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
