import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes54

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9376 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 0, 1, -1], ![-2, 2, 1, -1]]

def raw9376step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9376 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9376 = injectiveMoment H node3043 := by
  calc
    injectiveMoment H raw9376 = injectiveMoment H raw9376step0 := by
      have heq : raw9376step0 = (fun i j => raw9376 (permutation395 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9376 permutation395 permutation14
    _ = injectiveMoment H node3043 := by rfl

def raw9377 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 0, 2, -2], ![-2, 2, 0, 0]]

def raw9377step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9377 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9377 = injectiveMoment H node3155 := by
  calc
    injectiveMoment H raw9377 = injectiveMoment H raw9377step0 := by
      have heq : raw9377step0 = (fun i j => raw9377 (permutation395 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9377 permutation395 permutation14
    _ = injectiveMoment H node3155 := by rfl

def raw9378 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 2, 2, -4]]

def raw9378step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9378 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9378 = injectiveMoment H node3054 := by
  calc
    injectiveMoment H raw9378 = injectiveMoment H raw9378step0 := by
      have heq : raw9378step0 = (fun i j => raw9378 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9378 permutation262 permutation9
    _ = injectiveMoment H node3054 := by rfl

def raw9379 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw9379step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -1, -3, 4]]

def raw9379step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem canonical9379 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9379 = injectiveMoment H node3413 := by
  calc
    injectiveMoment H raw9379 = injectiveMoment H raw9379step0 := by
      have heq : raw9379step0 = -raw9379 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9379).symm
    injectiveMoment H raw9379step0 = injectiveMoment H raw9379step1 := by
      have heq : raw9379step1 = (fun i j => raw9379step0 (permutation374 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9379step0 permutation374 permutation15
    _ = injectiveMoment H node3413 := by rfl

def raw9380 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 1, 2, -3]]

def raw9380step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -1, -2, 3]]

def raw9380step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

theorem canonical9380 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9380 = injectiveMoment H node3417 := by
  calc
    injectiveMoment H raw9380 = injectiveMoment H raw9380step0 := by
      have heq : raw9380step0 = -raw9380 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9380).symm
    injectiveMoment H raw9380step0 = injectiveMoment H raw9380step1 := by
      have heq : raw9380step1 = (fun i j => raw9380step0 (permutation374 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9380step0 permutation374 permutation15
    _ = injectiveMoment H node3417 := by rfl

def raw9381 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 0, 3, -3]]

def raw9381step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

theorem canonical9381 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9381 = injectiveMoment H node3465 := by
  calc
    injectiveMoment H raw9381 = injectiveMoment H raw9381step0 := by
      have heq : raw9381step0 = (fun i j => raw9381 (permutation235 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9381 permutation235 permutation16
    _ = injectiveMoment H node3465 := by rfl

def raw9382 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![-1, 2, 2, -3]]

def raw9382step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, -1, -1], ![1, -2, -2, 3]]

def raw9382step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical9382 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9382 = injectiveMoment H node3230 := by
  calc
    injectiveMoment H raw9382 = injectiveMoment H raw9382step0 := by
      have heq : raw9382step0 = -raw9382 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9382).symm
    injectiveMoment H raw9382step0 = injectiveMoment H raw9382step1 := by
      have heq : raw9382step1 = (fun i j => raw9382step0 (permutation373 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9382step0 permutation373 permutation15
    _ = injectiveMoment H node3230 := by rfl

def raw9383 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 2, 2, -3]]

def raw9383step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -2, -2, 3]]

def raw9383step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical9383 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9383 = injectiveMoment H node2886 := by
  calc
    injectiveMoment H raw9383 = injectiveMoment H raw9383step0 := by
      have heq : raw9383step0 = -raw9383 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9383).symm
    injectiveMoment H raw9383step0 = injectiveMoment H raw9383step1 := by
      have heq : raw9383step1 = (fun i j => raw9383step0 (permutation387 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9383step0 permutation387 permutation23
    _ = injectiveMoment H node2886 := by rfl

def raw9384 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 1, 1], ![-1, 2, 1, -2]]

def raw9384step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, -1, -1], ![1, -2, -1, 2]]

def raw9384step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical9384 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9384 = injectiveMoment H node3078 := by
  calc
    injectiveMoment H raw9384 = injectiveMoment H raw9384step0 := by
      have heq : raw9384step0 = -raw9384 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9384).symm
    injectiveMoment H raw9384step0 = injectiveMoment H raw9384step1 := by
      have heq : raw9384step1 = (fun i j => raw9384step0 (permutation374 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9384step0 permutation374 permutation17
    _ = injectiveMoment H node3078 := by rfl

def raw9385 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 0, 0]]

def raw9385step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 0, 0]]

def raw9385step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical9385 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9385 = injectiveMoment H node2743 := by
  calc
    injectiveMoment H raw9385 = injectiveMoment H raw9385step0 := by
      have hz : ∀ j, raw9385 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9385step0 = (fun i j => raw9385 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9385 permutation202 hz
    injectiveMoment H raw9385step0 = injectiveMoment H raw9385step1 := by
      have heq : raw9385step1 = (fun i j => raw9385step0 (permutation48 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9385step0 permutation48 permutation21
    _ = injectiveMoment H node2743 := by rfl

def raw9386 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 1, 0], ![2, -2, -1, 1]]

def raw9386step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, -1, -1, 0], ![-2, 2, 1, -1]]

def raw9386step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, -1, -1, 0], ![-2, 2, 1, -1]]

def raw9386step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9386 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9386 = injectiveMoment H node1747 := by
  calc
    injectiveMoment H raw9386 = injectiveMoment H raw9386step0 := by
      have heq : raw9386step0 = -raw9386 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9386).symm
    injectiveMoment H raw9386step0 = injectiveMoment H raw9386step1 := by
      have hz : ∀ j, raw9386step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9386step1 = (fun i j => raw9386step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9386step0 permutation202 hz
    injectiveMoment H raw9386step1 = injectiveMoment H raw9386step2 := by
      have heq : raw9386step2 = (fun i j => raw9386step1 (permutation128 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9386step1 permutation128 permutation14
    _ = injectiveMoment H node1747 := by rfl

def raw9387 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 2, 0, -3]]

def raw9387step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 2, 0, -3]]

def raw9387step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical9387 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9387 = injectiveMoment H node2738 := by
  calc
    injectiveMoment H raw9387 = injectiveMoment H raw9387step0 := by
      have hz : ∀ j, raw9387 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9387step0 = (fun i j => raw9387 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9387 permutation202 hz
    injectiveMoment H raw9387step0 = injectiveMoment H raw9387step1 := by
      have heq : raw9387step1 = (fun i j => raw9387step0 (permutation48 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9387step0 permutation48 permutation21
    _ = injectiveMoment H node2738 := by rfl

def raw9388 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 0, 0]]

def raw9388step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 0, 0]]

def raw9388step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

theorem canonical9388 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9388 = injectiveMoment H node2851 := by
  calc
    injectiveMoment H raw9388 = injectiveMoment H raw9388step0 := by
      have hz : ∀ j, raw9388 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9388step0 = (fun i j => raw9388 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9388 permutation202 hz
    injectiveMoment H raw9388step0 = injectiveMoment H raw9388step1 := by
      have heq : raw9388step1 = (fun i j => raw9388step0 (permutation54 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9388step0 permutation54 permutation25
    _ = injectiveMoment H node2851 := by rfl

def raw9389 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 2, -2]]

def raw9389step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![2, 0, 0, -2], ![-2, 2, -2, 2]]

def raw9389step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![2, 0, 0, -2], ![-2, 2, -2, 2]]

def raw9389step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical9389 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9389 = injectiveMoment H node1518 := by
  calc
    injectiveMoment H raw9389 = injectiveMoment H raw9389step0 := by
      have heq : raw9389step0 = -raw9389 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9389).symm
    injectiveMoment H raw9389step0 = injectiveMoment H raw9389step1 := by
      have hz : ∀ j, raw9389step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9389step1 = (fun i j => raw9389step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9389step0 permutation202 hz
    injectiveMoment H raw9389step1 = injectiveMoment H raw9389step2 := by
      have heq : raw9389step2 = (fun i j => raw9389step1 (permutation141 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9389step1 permutation141 permutation11
    _ = injectiveMoment H node1518 := by rfl

def raw9390 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 1, -1]]

def raw9390step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 1, 0], ![0, -1, 0, 1], ![2, 0, -1, -1], ![-2, 2, -1, 1]]

def raw9390step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![2, 0, -1, -1], ![-2, 2, -1, 1]]

def raw9390step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical9390 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9390 = injectiveMoment H node1786 := by
  calc
    injectiveMoment H raw9390 = injectiveMoment H raw9390step0 := by
      have heq : raw9390step0 = -raw9390 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9390).symm
    injectiveMoment H raw9390step0 = injectiveMoment H raw9390step1 := by
      have hz : ∀ j, raw9390step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9390step1 = (fun i j => raw9390step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9390step0 permutation202 hz
    injectiveMoment H raw9390step1 = injectiveMoment H raw9390step2 := by
      have heq : raw9390step2 = (fun i j => raw9390step1 (permutation139 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9390step1 permutation139 permutation12
    _ = injectiveMoment H node1786 := by rfl

def raw9391 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 2, 1]]

def raw9391step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 2, 1]]

def raw9391step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical9391 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9391 = injectiveMoment H node1786 := by
  calc
    injectiveMoment H raw9391 = injectiveMoment H raw9391step0 := by
      have hz : ∀ j, raw9391 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9391step0 = (fun i j => raw9391 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9391 permutation202 hz
    injectiveMoment H raw9391step0 = injectiveMoment H raw9391step1 := by
      have heq : raw9391step1 = (fun i j => raw9391step0 (permutation130 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9391step0 permutation130 permutation10
    _ = injectiveMoment H node1786 := by rfl

def raw9392 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 1, 2], ![1, 1, 1, -3]]

def raw9392step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 1, 2], ![1, 1, 1, -3]]

def raw9392step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical9392 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9392 = injectiveMoment H node1768 := by
  calc
    injectiveMoment H raw9392 = injectiveMoment H raw9392step0 := by
      have hz : ∀ j, raw9392 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9392step0 = (fun i j => raw9392 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9392 permutation202 hz
    injectiveMoment H raw9392step0 = injectiveMoment H raw9392step1 := by
      have heq : raw9392step1 = (fun i j => raw9392step0 (permutation104 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9392step0 permutation104 permutation9
    _ = injectiveMoment H node1768 := by rfl

def raw9393 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 2, 1]]

def raw9393step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 2, 1]]

def raw9393step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical9393 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9393 = injectiveMoment H node1793 := by
  calc
    injectiveMoment H raw9393 = injectiveMoment H raw9393step0 := by
      have hz : ∀ j, raw9393 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9393step0 = (fun i j => raw9393 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9393 permutation202 hz
    injectiveMoment H raw9393step0 = injectiveMoment H raw9393step1 := by
      have heq : raw9393step1 = (fun i j => raw9393step0 (permutation128 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9393step0 permutation128 permutation10
    _ = injectiveMoment H node1793 := by rfl

def raw9394 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9394step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![2, 1, 0, -3], ![-2, 1, -1, 2]]

def raw9394step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![2, 1, 0, -3], ![-2, 1, -1, 2]]

def raw9394step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical9394 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9394 = injectiveMoment H node2436 := by
  calc
    injectiveMoment H raw9394 = injectiveMoment H raw9394step0 := by
      have heq : raw9394step0 = -raw9394 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9394).symm
    injectiveMoment H raw9394step0 = injectiveMoment H raw9394step1 := by
      have hz : ∀ j, raw9394step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9394step1 = (fun i j => raw9394step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9394step0 permutation202 hz
    injectiveMoment H raw9394step1 = injectiveMoment H raw9394step2 := by
      have heq : raw9394step2 = (fun i j => raw9394step1 (permutation136 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9394step1 permutation136 permutation21
    _ = injectiveMoment H node2436 := by rfl

def raw9395 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 1, -1]]

def raw9395step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![2, 0, 0, -2], ![-2, 2, -1, 1]]

def raw9395step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![2, 0, 0, -2], ![-2, 2, -1, 1]]

def raw9395step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical9395 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9395 = injectiveMoment H node2455 := by
  calc
    injectiveMoment H raw9395 = injectiveMoment H raw9395step0 := by
      have heq : raw9395step0 = -raw9395 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9395).symm
    injectiveMoment H raw9395step0 = injectiveMoment H raw9395step1 := by
      have hz : ∀ j, raw9395step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9395step1 = (fun i j => raw9395step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9395step0 permutation202 hz
    injectiveMoment H raw9395step1 = injectiveMoment H raw9395step2 := by
      have heq : raw9395step2 = (fun i j => raw9395step1 (permutation136 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9395step1 permutation136 permutation21
    _ = injectiveMoment H node2455 := by rfl

def raw9396 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 0, 0]]

def raw9396step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![2, 0, -1, -1], ![-2, 2, 0, 0]]

def raw9396step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![2, 0, -1, -1], ![-2, 2, 0, 0]]

def raw9396step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical9396 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9396 = injectiveMoment H node2613 := by
  calc
    injectiveMoment H raw9396 = injectiveMoment H raw9396step0 := by
      have heq : raw9396step0 = -raw9396 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9396).symm
    injectiveMoment H raw9396step0 = injectiveMoment H raw9396step1 := by
      have hz : ∀ j, raw9396step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9396step1 = (fun i j => raw9396step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9396step0 permutation202 hz
    injectiveMoment H raw9396step1 = injectiveMoment H raw9396step2 := by
      have heq : raw9396step2 = (fun i j => raw9396step1 (permutation125 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9396step1 permutation125 permutation26
    _ = injectiveMoment H node2613 := by rfl

def raw9397 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 2, 0], ![2, -2, -1, 1]]

def raw9397step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![2, 0, -2, 0], ![-2, 2, 1, -1]]

def raw9397step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![2, 0, -2, 0], ![-2, 2, 1, -1]]

def raw9397step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical9397 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9397 = injectiveMoment H node1749 := by
  calc
    injectiveMoment H raw9397 = injectiveMoment H raw9397step0 := by
      have heq : raw9397step0 = -raw9397 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9397).symm
    injectiveMoment H raw9397step0 = injectiveMoment H raw9397step1 := by
      have hz : ∀ j, raw9397step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9397step1 = (fun i j => raw9397step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9397step0 permutation202 hz
    injectiveMoment H raw9397step1 = injectiveMoment H raw9397step2 := by
      have heq : raw9397step2 = (fun i j => raw9397step1 (permutation128 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9397step1 permutation128 permutation14
    _ = injectiveMoment H node1749 := by rfl

def raw9398 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 2, 1]]

def raw9398step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 2, 1]]

def raw9398step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem canonical9398 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9398 = injectiveMoment H node1785 := by
  calc
    injectiveMoment H raw9398 = injectiveMoment H raw9398step0 := by
      have hz : ∀ j, raw9398 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9398step0 = (fun i j => raw9398 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9398 permutation202 hz
    injectiveMoment H raw9398step0 = injectiveMoment H raw9398step1 := by
      have heq : raw9398step1 = (fun i j => raw9398step0 (permutation128 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9398step0 permutation128 permutation10
    _ = injectiveMoment H node1785 := by rfl

def raw9399 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 1, 2]]

def raw9399step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 1, 2]]

def raw9399step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem canonical9399 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9399 = injectiveMoment H node2778 := by
  calc
    injectiveMoment H raw9399 = injectiveMoment H raw9399step0 := by
      have hz : ∀ j, raw9399 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9399step0 = (fun i j => raw9399 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9399 permutation202 hz
    injectiveMoment H raw9399step0 = injectiveMoment H raw9399step1 := by
      have heq : raw9399step1 = (fun i j => raw9399step0 (permutation45 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9399step0 permutation45 permutation23
    _ = injectiveMoment H node2778 := by rfl

def raw9400 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 2, 2]]

def raw9400step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 2, 2]]

def raw9400step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9400 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9400 = injectiveMoment H node1521 := by
  calc
    injectiveMoment H raw9400 = injectiveMoment H raw9400step0 := by
      have hz : ∀ j, raw9400 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9400step0 = (fun i j => raw9400 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9400 permutation202 hz
    injectiveMoment H raw9400step0 = injectiveMoment H raw9400step1 := by
      have heq : raw9400step1 = (fun i j => raw9400step0 (permutation128 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9400step0 permutation128 permutation9
    _ = injectiveMoment H node1521 := by rfl

def raw9401 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 1, 3]]

def raw9401step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 1, 3]]

def raw9401step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -2, 3]]

theorem canonical9401 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9401 = injectiveMoment H node2786 := by
  calc
    injectiveMoment H raw9401 = injectiveMoment H raw9401step0 := by
      have hz : ∀ j, raw9401 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9401step0 = (fun i j => raw9401 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9401 permutation202 hz
    injectiveMoment H raw9401step0 = injectiveMoment H raw9401step1 := by
      have heq : raw9401step1 = (fun i j => raw9401step0 (permutation33 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9401step0 permutation33 permutation21
    _ = injectiveMoment H node2786 := by rfl

def raw9402 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, -1, 1, -1]]

def raw9402step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, -1, 0, -1], ![-1, 1, -1, 1]]

def raw9402step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![2, -1, 0, -1], ![-1, 1, -1, 1]]

def raw9402step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical9402 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9402 = injectiveMoment H node2630 := by
  calc
    injectiveMoment H raw9402 = injectiveMoment H raw9402step0 := by
      have heq : raw9402step0 = -raw9402 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9402).symm
    injectiveMoment H raw9402step0 = injectiveMoment H raw9402step1 := by
      have hz : ∀ j, raw9402step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9402step1 = (fun i j => raw9402step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9402step0 permutation202 hz
    injectiveMoment H raw9402step1 = injectiveMoment H raw9402step2 := by
      have heq : raw9402step2 = (fun i j => raw9402step1 (permutation142 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9402step1 permutation142 permutation22
    _ = injectiveMoment H node2630 := by rfl

def raw9403 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 1, 0]]

def raw9403step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, -1, -1, 0]]

def raw9403step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, -1, -1, 0]]

def raw9403step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical9403 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9403 = injectiveMoment H node2734 := by
  calc
    injectiveMoment H raw9403 = injectiveMoment H raw9403step0 := by
      have heq : raw9403step0 = -raw9403 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9403).symm
    injectiveMoment H raw9403step0 = injectiveMoment H raw9403step1 := by
      have hz : ∀ j, raw9403step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9403step1 = (fun i j => raw9403step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9403step0 permutation202 hz
    injectiveMoment H raw9403step1 = injectiveMoment H raw9403step2 := by
      have heq : raw9403step2 = (fun i j => raw9403step1 (permutation144 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9403step1 permutation144 permutation26
    _ = injectiveMoment H node2734 := by rfl

def raw9404 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, -2, 2, -1]]

def raw9404step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, -2, 2, -1]]

def raw9404step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical9404 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9404 = injectiveMoment H node1793 := by
  calc
    injectiveMoment H raw9404 = injectiveMoment H raw9404step0 := by
      have hz : ∀ j, raw9404 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9404step0 = (fun i j => raw9404 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9404 permutation202 hz
    injectiveMoment H raw9404step0 = injectiveMoment H raw9404step1 := by
      have heq : raw9404step1 = (fun i j => raw9404step0 (permutation139 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9404step0 permutation139 permutation19
    _ = injectiveMoment H node1793 := by rfl

def raw9405 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![1, -2, 2, -1]]

def raw9405step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![1, -2, 2, -1]]

def raw9405step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

theorem canonical9405 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9405 = injectiveMoment H node1738 := by
  calc
    injectiveMoment H raw9405 = injectiveMoment H raw9405step0 := by
      have hz : ∀ j, raw9405 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9405step0 = (fun i j => raw9405 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9405 permutation202 hz
    injectiveMoment H raw9405step0 = injectiveMoment H raw9405step1 := by
      have heq : raw9405step1 = (fun i j => raw9405step0 (permutation104 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9405step0 permutation104 permutation11
    _ = injectiveMoment H node1738 := by rfl

def raw9406 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -2, 1, 0]]

def raw9406step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![2, -1, 0, -1], ![-1, 2, -1, 0]]

def raw9406step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![2, -1, 0, -1], ![-1, 2, -1, 0]]

def raw9406step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical9406 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9406 = injectiveMoment H node2584 := by
  calc
    injectiveMoment H raw9406 = injectiveMoment H raw9406step0 := by
      have heq : raw9406step0 = -raw9406 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9406).symm
    injectiveMoment H raw9406step0 = injectiveMoment H raw9406step1 := by
      have hz : ∀ j, raw9406step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9406step1 = (fun i j => raw9406step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9406step0 permutation202 hz
    injectiveMoment H raw9406step1 = injectiveMoment H raw9406step2 := by
      have heq : raw9406step2 = (fun i j => raw9406step1 (permutation142 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9406step1 permutation142 permutation22
    _ = injectiveMoment H node2584 := by rfl

def raw9407 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def raw9407step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw9407step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw9407step2 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical9407 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9407 = injectiveMoment H node2427 := by
  calc
    injectiveMoment H raw9407 = injectiveMoment H raw9407step0 := by
      have heq : raw9407step0 = -raw9407 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9407).symm
    injectiveMoment H raw9407step0 = injectiveMoment H raw9407step1 := by
      have hz : ∀ j, raw9407step0 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9407step1 = (fun i j => raw9407step0 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9407step0 permutation202 hz
    injectiveMoment H raw9407step1 = injectiveMoment H raw9407step2 := by
      have heq : raw9407step2 = (fun i j => raw9407step1 (permutation148 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9407step1 permutation148 permutation23
    _ = injectiveMoment H node2427 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
