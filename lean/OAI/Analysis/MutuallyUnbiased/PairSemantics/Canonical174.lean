import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5568 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical5568 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5568 = injectiveMoment H node754 := by
  rfl

def raw5569 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![1, 2, 0, -3]]

def raw5569step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-2, 2, 0], ![5, -2, -3]]

def raw5569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical5569 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5569 = injectiveMoment H node120 := by
  calc
    injectiveMoment H raw5569 = injectiveMoment H raw5569step0 := by
      have heq : raw5569step0 = raw5569.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5569).symm
    injectiveMoment H raw5569step0 = injectiveMoment H raw5569step1 := by
      have heq : raw5569step1 = (fun i j => raw5569step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5569step0 permutation27 permutation6
    _ = injectiveMoment H node120 := by rfl

def raw5570 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw5570step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem canonical5570 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5570 = injectiveMoment H node750 := by
  calc
    injectiveMoment H raw5570 = injectiveMoment H raw5570step0 := by
      have heq : raw5570step0 = (fun i j => raw5570 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5570 permutation9 permutation11
    _ = injectiveMoment H node750 := by rfl

def raw5571 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw5571step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![-2, 0, 2, 0], ![5, -1, -3, -1]]

def raw5571step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical5571 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5571 = injectiveMoment H node890 := by
  calc
    injectiveMoment H raw5571 = injectiveMoment H raw5571step0 := by
      have heq : raw5571step0 = raw5571.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5571).symm
    injectiveMoment H raw5571step0 = injectiveMoment H raw5571step1 := by
      have heq : raw5571step1 = (fun i j => raw5571step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5571step0 permutation31 permutation20
    _ = injectiveMoment H node890 := by rfl

def raw5572 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical5572 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5572 = injectiveMoment H node755 := by
  rfl

def raw5573 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 1, 1, -2], ![1, 1, 1, -3]]

def raw5573step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1], ![5, -2, -3]]

def raw5573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical5573 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5573 = injectiveMoment H node124 := by
  calc
    injectiveMoment H raw5573 = injectiveMoment H raw5573step0 := by
      have heq : raw5573step0 = raw5573.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5573).symm
    injectiveMoment H raw5573step0 = injectiveMoment H raw5573step1 := by
      have heq : raw5573step1 = (fun i j => raw5573step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5573step0 permutation27 permutation6
    _ = injectiveMoment H node124 := by rfl

def raw5574 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 1, 2, -3], ![1, 1, 0, -2]]

def raw5574step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-2, 2, 0], ![5, -3, -2]]

def raw5574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical5574 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5574 = injectiveMoment H node127 := by
  calc
    injectiveMoment H raw5574 = injectiveMoment H raw5574step0 := by
      have heq : raw5574step0 = raw5574.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5574).symm
    injectiveMoment H raw5574step0 = injectiveMoment H raw5574step1 := by
      have heq : raw5574step1 = (fun i j => raw5574step0 (permutation31 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5574step0 permutation31 permutation8
    _ = injectiveMoment H node127 := by rfl

def raw5575 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 2, 0, -2], ![1, 0, 2, -3]]

def raw5575step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2], ![5, -2, -3]]

def raw5575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical5575 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5575 = injectiveMoment H node120 := by
  calc
    injectiveMoment H raw5575 = injectiveMoment H raw5575step0 := by
      have heq : raw5575step0 = raw5575.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5575).symm
    injectiveMoment H raw5575step0 = injectiveMoment H raw5575step1 := by
      have heq : raw5575step1 = (fun i j => raw5575step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5575step0 permutation28 permutation6
    _ = injectiveMoment H node120 := by rfl

def raw5576 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def raw5576step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1], ![5, -3, -2]]

def raw5576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical5576 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5576 = injectiveMoment H node127 := by
  calc
    injectiveMoment H raw5576 = injectiveMoment H raw5576step0 := by
      have heq : raw5576step0 = raw5576.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5576).symm
    injectiveMoment H raw5576step0 = injectiveMoment H raw5576step1 := by
      have heq : raw5576step1 = (fun i j => raw5576step0 (permutation29 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5576step0 permutation29 permutation8
    _ = injectiveMoment H node127 := by rfl

def raw5577 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![1, 0, 2, -3], ![0, 2, 0, -2]]

def raw5577step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-2, 2, 0], ![5, -3, -2]]

def raw5577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical5577 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5577 = injectiveMoment H node120 := by
  calc
    injectiveMoment H raw5577 = injectiveMoment H raw5577step0 := by
      have heq : raw5577step0 = raw5577.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5577).symm
    injectiveMoment H raw5577step0 = injectiveMoment H raw5577step1 := by
      have heq : raw5577step1 = (fun i j => raw5577step0 (permutation28 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5577step0 permutation28 permutation8
    _ = injectiveMoment H node120 := by rfl

def raw5578 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![1, 1, 1, -3], ![0, 1, 1, -2]]

def raw5578step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1], ![5, -3, -2]]

def raw5578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical5578 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5578 = injectiveMoment H node124 := by
  calc
    injectiveMoment H raw5578 = injectiveMoment H raw5578step0 := by
      have heq : raw5578step0 = raw5578.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5578).symm
    injectiveMoment H raw5578step0 = injectiveMoment H raw5578step1 := by
      have heq : raw5578step1 = (fun i j => raw5578step0 (permutation27 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5578step0 permutation27 permutation8
    _ = injectiveMoment H node124 := by rfl

def raw5579 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

theorem canonical5579 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5579 = injectiveMoment H node2388 := by
  rfl

def raw5580 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 0, 0], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def raw5580step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 0, 2], ![-1, 0, 1, 0], ![4, 0, -1, -3]]

def raw5580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![4, -1, -3]]

def raw5580step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5580 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5580 = injectiveMoment H node254 := by
  calc
    injectiveMoment H raw5580 = injectiveMoment H raw5580step0 := by
      have heq : raw5580step0 = raw5580.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5580).symm
    injectiveMoment H raw5580step0 = injectiveMoment H raw5580step1 := by
      have hz : ∀ i, raw5580step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw5580step1 = (fun i j => raw5580step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5580step0 permutation15 hz
    injectiveMoment H raw5580step1 = injectiveMoment H raw5580step2 := by
      have heq : raw5580step2 = (fun i j => raw5580step1 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5580step1 permutation27 permutation6
    _ = injectiveMoment H node254 := by rfl

def raw5581 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 0, 0], ![1, 2, 0, -3]]

def raw5581step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 0, 2], ![-1, 1, 0, 0], ![4, -1, 0, -3]]

def raw5581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![4, -1, -3]]

def raw5581step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5581 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5581 = injectiveMoment H node254 := by
  calc
    injectiveMoment H raw5581 = injectiveMoment H raw5581step0 := by
      have heq : raw5581step0 = raw5581.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5581).symm
    injectiveMoment H raw5581step0 = injectiveMoment H raw5581step1 := by
      have hz : ∀ i, raw5581step0 i (permutation21 0) = 0 := by decide +kernel
      have heq : raw5581step1 = (fun i j => raw5581step0 i (permutation21 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5581step0 permutation21 hz
    injectiveMoment H raw5581step1 = injectiveMoment H raw5581step2 := by
      have heq : raw5581step2 = (fun i j => raw5581step1 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5581step1 permutation27 permutation6
    _ = injectiveMoment H node254 := by rfl

def raw5582 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical5582 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5582 = injectiveMoment H node2391 := by
  rfl

def raw5583 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical5583 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5583 = injectiveMoment H node2392 := by
  rfl

def raw5584 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical5584 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5584 = injectiveMoment H node2393 := by
  rfl

def raw5585 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical5585 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5585 = injectiveMoment H node2394 := by
  rfl

def raw5586 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical5586 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5586 = injectiveMoment H node2395 := by
  rfl

def raw5587 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -1, -2]]

def raw5587step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 0, 2], ![-1, 1, 1, -1], ![4, -1, -1, -2]]

def raw5587step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical5587 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5587 = injectiveMoment H node907 := by
  calc
    injectiveMoment H raw5587 = injectiveMoment H raw5587step0 := by
      have heq : raw5587step0 = raw5587.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5587).symm
    injectiveMoment H raw5587step0 = injectiveMoment H raw5587step1 := by
      have heq : raw5587step1 = (fun i j => raw5587step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5587step0 permutation27 permutation18
    _ = injectiveMoment H node907 := by rfl

def raw5588 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical5588 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5588 = injectiveMoment H node2396 := by
  rfl

def raw5589 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical5589 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5589 = injectiveMoment H node2397 := by
  rfl

def raw5590 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical5590 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5590 = injectiveMoment H node2398 := by
  rfl

def raw5591 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 2, -2, -1]]

theorem canonical5591 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5591 = injectiveMoment H node765 := by
  rfl

def raw5592 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical5592 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5592 = injectiveMoment H node2399 := by
  rfl

def raw5593 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical5593 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5593 = injectiveMoment H node2400 := by
  rfl

def raw5594 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def raw5594step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 0, 1, 1], ![-1, 1, -1, 1], ![4, -1, 0, -3]]

def raw5594step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical5594 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5594 = injectiveMoment H node1176 := by
  calc
    injectiveMoment H raw5594 = injectiveMoment H raw5594step0 := by
      have heq : raw5594step0 = raw5594.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5594).symm
    injectiveMoment H raw5594step0 = injectiveMoment H raw5594step1 := by
      have heq : raw5594step1 = (fun i j => raw5594step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5594step0 permutation27 permutation18
    _ = injectiveMoment H node1176 := by rfl

def raw5595 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw5595step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical5595 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5595 = injectiveMoment H node2503 := by
  calc
    injectiveMoment H raw5595 = injectiveMoment H raw5595step0 := by
      have heq : raw5595step0 = (fun i j => raw5595 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5595 permutation41 permutation11
    _ = injectiveMoment H node2503 := by rfl

def raw5596 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw5596step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical5596 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5596 = injectiveMoment H node910 := by
  calc
    injectiveMoment H raw5596 = injectiveMoment H raw5596step0 := by
      have heq : raw5596step0 = (fun i j => raw5596 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5596 permutation11 permutation11
    _ = injectiveMoment H node910 := by rfl

def raw5597 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical5597 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5597 = injectiveMoment H node766 := by
  rfl

def raw5598 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, 1, -2, 0]]

theorem canonical5598 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5598 = injectiveMoment H node767 := by
  rfl

def raw5599 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 2, -3]]

theorem canonical5599 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5599 = injectiveMoment H node768 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
