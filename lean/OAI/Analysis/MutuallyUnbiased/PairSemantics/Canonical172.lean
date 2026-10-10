import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5504 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def raw5504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5504 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5504 = injectiveMoment H node744 := by
  calc
    injectiveMoment H raw5504 = injectiveMoment H raw5504step0 := by
      have heq : raw5504step0 = (fun i j => raw5504 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5504 permutation34 permutation3
    _ = injectiveMoment H node744 := by rfl

def raw5505 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical5505 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5505 = injectiveMoment H node247 := by
  rfl

def raw5506 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical5506 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5506 = injectiveMoment H node248 := by
  rfl

def raw5507 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![2, 0, -2]]

def raw5507step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![4, -2, -2]]

def raw5507step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical5507 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5507 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw5507 = injectiveMoment H raw5507step0 := by
      have heq : raw5507step0 = raw5507.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5507).symm
    injectiveMoment H raw5507step0 = injectiveMoment H raw5507step1 := by
      have heq : raw5507step1 = (fun i j => raw5507step0 (permutation8 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5507step0 permutation8 permutation8
    _ = injectiveMoment H node32 := by rfl

def raw5508 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 4, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical5508 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5508 = injectiveMoment H node745 := by
  rfl

def raw5509 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 4, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5509 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5509 = injectiveMoment H node249 := by
  rfl

def raw5510 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 4, -3], ![1, 0, -1], ![1, -1, 0]]

def raw5510step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 4, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5510 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5510 = injectiveMoment H node249 := by
  calc
    injectiveMoment H raw5510 = injectiveMoment H raw5510step0 := by
      have heq : raw5510step0 = (fun i j => raw5510 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5510 permutation10 permutation3
    _ = injectiveMoment H node249 := by rfl

def raw5511 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 4, -3], ![2, -1, -1]]

def raw5511step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -4, 3], ![-2, 1, 1]]

def raw5511step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -4, 3], ![1, 3, -4]]

theorem canonical5511 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5511 = injectiveMoment H node42 := by
  calc
    injectiveMoment H raw5511 = injectiveMoment H raw5511step0 := by
      have heq : raw5511step0 = -raw5511 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5511).symm
    injectiveMoment H raw5511step0 = injectiveMoment H raw5511step1 := by
      have heq : raw5511step1 = (fun i j => raw5511step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5511step0 permutation8 permutation3
    _ = injectiveMoment H node42 := by rfl

def raw5512 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]

theorem canonical5512 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5512 = injectiveMoment H node746 := by
  rfl

def raw5513 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical5513 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5513 = injectiveMoment H node747 := by
  rfl

def raw5514 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 2, -2], ![1, 2, -3]]

theorem canonical5514 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5514 = injectiveMoment H node250 := by
  rfl

def raw5515 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

theorem canonical5515 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5515 = injectiveMoment H node252 := by
  rfl

def raw5516 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![1, 1, -2], ![0, 3, -3]]

def raw5516step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 3, -3], ![1, 1, -2]]

theorem canonical5516 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5516 = injectiveMoment H node251 := by
  calc
    injectiveMoment H raw5516 = injectiveMoment H raw5516step0 := by
      have heq : raw5516step0 = (fun i j => raw5516 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5516 permutation10 permutation3
    _ = injectiveMoment H node251 := by rfl

def raw5517 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 0, 0], ![0, 1, -1], ![1, 2, -3]]

def raw5517step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 2, -3]]

theorem canonical5517 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5517 = injectiveMoment H node51 := by
  calc
    injectiveMoment H raw5517 = injectiveMoment H raw5517step0 := by
      have hz : ∀ j, raw5517 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5517step0 = (fun i j => raw5517 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5517 permutation15 hz
    _ = injectiveMoment H node51 := by rfl

def raw5518 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 0, 0], ![0, 3, -3], ![1, 0, -1]]

def raw5518step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![1, 0, -1]]

theorem canonical5518 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5518 = injectiveMoment H node53 := by
  calc
    injectiveMoment H raw5518 = injectiveMoment H raw5518step0 := by
      have hz : ∀ j, raw5518 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5518step0 = (fun i j => raw5518 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5518 permutation15 hz
    _ = injectiveMoment H node53 := by rfl

def raw5519 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 0, 0], ![1, 3, -4]]

def raw5519step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 0, 3], ![4, 0, -4]]

def raw5519step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![4, -4]]

def raw5519step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

theorem canonical5519 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5519 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw5519 = injectiveMoment H raw5519step0 := by
      have heq : raw5519step0 = raw5519.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5519).symm
    injectiveMoment H raw5519step0 = injectiveMoment H raw5519step1 := by
      have hz : ∀ i, raw5519step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw5519step1 = (fun i j => raw5519step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw5519step0 permutation5 hz
    injectiveMoment H raw5519step1 = injectiveMoment H raw5519step2 := by
      have heq : raw5519step2 = (fun i j => raw5519step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5519step1 permutation7 permutation2
    _ = injectiveMoment H node8 := by rfl

def raw5520 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw5520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical5520 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5520 = injectiveMoment H node737 := by
  calc
    injectiveMoment H raw5520 = injectiveMoment H raw5520step0 := by
      have heq : raw5520step0 = (fun i j => raw5520 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5520 permutation39 permutation3
    _ = injectiveMoment H node737 := by rfl

def raw5521 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def raw5521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical5521 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5521 = injectiveMoment H node741 := by
  calc
    injectiveMoment H raw5521 = injectiveMoment H raw5521step0 := by
      have heq : raw5521step0 = (fun i j => raw5521 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5521 permutation39 permutation3
    _ = injectiveMoment H node741 := by rfl

def raw5522 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1]]

def raw5522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical5522 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5522 = injectiveMoment H node742 := by
  calc
    injectiveMoment H raw5522 = injectiveMoment H raw5522step0 := by
      have heq : raw5522step0 = (fun i j => raw5522 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5522 permutation39 permutation3
    _ = injectiveMoment H node742 := by rfl

def raw5523 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def raw5523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5523 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5523 = injectiveMoment H node744 := by
  calc
    injectiveMoment H raw5523 = injectiveMoment H raw5523step0 := by
      have heq : raw5523step0 = (fun i j => raw5523 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5523 permutation39 permutation3
    _ = injectiveMoment H node744 := by rfl

def raw5524 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3]]

def raw5524step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 2, -3]]

theorem canonical5524 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5524 = injectiveMoment H node51 := by
  calc
    injectiveMoment H raw5524 = injectiveMoment H raw5524step0 := by
      have hz : ∀ j, raw5524 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5524step0 = (fun i j => raw5524 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5524 permutation21 hz
    _ = injectiveMoment H node51 := by rfl

def raw5525 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2]]

def raw5525step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical5525 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5525 = injectiveMoment H node253 := by
  calc
    injectiveMoment H raw5525 = injectiveMoment H raw5525step0 := by
      have hz : ∀ j, raw5525 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5525step0 = (fun i j => raw5525 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5525 permutation104 hz
    _ = injectiveMoment H node253 := by rfl

def raw5526 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical5526 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5526 = injectiveMoment H node748 := by
  rfl

def raw5527 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical5527 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5527 = injectiveMoment H node749 := by
  rfl

def raw5528 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 2, -2]]

def raw5528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical5528 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5528 = injectiveMoment H node749 := by
  calc
    injectiveMoment H raw5528 = injectiveMoment H raw5528step0 := by
      have heq : raw5528step0 = (fun i j => raw5528 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5528 permutation34 permutation3
    _ = injectiveMoment H node749 := by rfl

def raw5529 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1]]

def raw5529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical5529 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5529 = injectiveMoment H node748 := by
  calc
    injectiveMoment H raw5529 = injectiveMoment H raw5529step0 := by
      have heq : raw5529step0 = (fun i j => raw5529 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5529 permutation34 permutation3
    _ = injectiveMoment H node748 := by rfl

def raw5530 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical5530 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5530 = injectiveMoment H node253 := by
  rfl

def raw5531 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1]]

def raw5531step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5531 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5531 = injectiveMoment H node254 := by
  calc
    injectiveMoment H raw5531 = injectiveMoment H raw5531step0 := by
      have hz : ∀ j, raw5531 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5531step0 = (fun i j => raw5531 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5531 permutation104 hz
    _ = injectiveMoment H node254 := by rfl

def raw5532 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0]]

def raw5532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical5532 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5532 = injectiveMoment H node749 := by
  calc
    injectiveMoment H raw5532 = injectiveMoment H raw5532step0 := by
      have heq : raw5532step0 = (fun i j => raw5532 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5532 permutation35 permutation3
    _ = injectiveMoment H node749 := by rfl

def raw5533 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![0, 1, -1]]

def raw5533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical5533 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5533 = injectiveMoment H node749 := by
  calc
    injectiveMoment H raw5533 = injectiveMoment H raw5533step0 := by
      have heq : raw5533step0 = (fun i j => raw5533 (permutation37 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5533 permutation37 permutation3
    _ = injectiveMoment H node749 := by rfl

def raw5534 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5534 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5534 = injectiveMoment H node254 := by
  rfl

def raw5535 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![0, 0, 0]]

def raw5535step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5535 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5535 = injectiveMoment H node254 := by
  calc
    injectiveMoment H raw5535 = injectiveMoment H raw5535step0 := by
      have hz : ∀ j, raw5535 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5535step0 = (fun i j => raw5535 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5535 permutation128 hz
    _ = injectiveMoment H node254 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
