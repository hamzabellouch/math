import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5472 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical5472 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5472 = injectiveMoment H node723 := by
  rfl

def raw5473 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5473 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5473 = injectiveMoment H node724 := by
  rfl

def raw5474 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 2, -2]]

def raw5474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5474 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5474 = injectiveMoment H node724 := by
  calc
    injectiveMoment H raw5474 = injectiveMoment H raw5474step0 := by
      have heq : raw5474step0 = (fun i j => raw5474 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5474 permutation34 permutation3
    _ = injectiveMoment H node724 := by rfl

def raw5475 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]

theorem canonical5475 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5475 = injectiveMoment H node237 := by
  rfl

def raw5476 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1]]

def raw5476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5476 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5476 = injectiveMoment H node724 := by
  calc
    injectiveMoment H raw5476 = injectiveMoment H raw5476step0 := by
      have heq : raw5476step0 = (fun i j => raw5476 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5476 permutation35 permutation3
    _ = injectiveMoment H node724 := by rfl

def raw5477 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 2, -2], ![1, 1, -2]]

theorem canonical5477 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5477 = injectiveMoment H node238 := by
  rfl

def raw5478 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical5478 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5478 = injectiveMoment H node239 := by
  rfl

def raw5479 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![1, 3, -4]]

theorem canonical5479 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5479 = injectiveMoment H node47 := by
  rfl

def raw5480 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def raw5480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5480 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5480 = injectiveMoment H node724 := by
  calc
    injectiveMoment H raw5480 = injectiveMoment H raw5480step0 := by
      have heq : raw5480step0 = (fun i j => raw5480 (permutation41 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5480 permutation41 permutation3
    _ = injectiveMoment H node724 := by rfl

def raw5481 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![0, 1, -1], ![1, 1, -2]]

def raw5481step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 2, -2], ![1, 1, -2]]

theorem canonical5481 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5481 = injectiveMoment H node238 := by
  calc
    injectiveMoment H raw5481 = injectiveMoment H raw5481step0 := by
      have heq : raw5481step0 = (fun i j => raw5481 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5481 permutation11 permutation3
    _ = injectiveMoment H node238 := by rfl

def raw5482 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5482 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5482 = injectiveMoment H node240 := by
  rfl

def raw5483 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![1, 2, -3]]

theorem canonical5483 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5483 = injectiveMoment H node48 := by
  rfl

def raw5484 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 3, -3], ![1, 1, -2]]

theorem canonical5484 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5484 = injectiveMoment H node49 := by
  rfl

def raw5485 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 4, -4], ![1, 0, -1]]

theorem canonical5485 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5485 = injectiveMoment H node50 := by
  rfl

def raw5486 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![1, 2, -3], ![0, 2, -2]]

def raw5486step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![1, 2, -3]]

theorem canonical5486 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5486 = injectiveMoment H node48 := by
  calc
    injectiveMoment H raw5486 = injectiveMoment H raw5486step0 := by
      have heq : raw5486step0 = (fun i j => raw5486 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5486 permutation4 permutation3
    _ = injectiveMoment H node48 := by rfl

def raw5487 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, -4, 5], ![1, 4, -5]]

def raw5487step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-4, 4], ![5, -5]]

def raw5487step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]

theorem canonical5487 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5487 = injectiveMoment H node6 := by
  calc
    injectiveMoment H raw5487 = injectiveMoment H raw5487step0 := by
      have heq : raw5487step0 = raw5487.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5487).symm
    injectiveMoment H raw5487step0 = injectiveMoment H raw5487step1 := by
      have heq : raw5487step1 = (fun i j => raw5487step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5487step0 permutation7 permutation2
    _ = injectiveMoment H node6 := by rfl

def raw5488 : Matrix (Fin 2) (Fin 4) ℤ := ![![-1, -3, 3, 1], ![1, 3, -3, -1]]

def raw5488step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![3, -3], ![1, -1]]

def raw5488step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

theorem canonical5488 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5488 = injectiveMoment H node24 := by
  calc
    injectiveMoment H raw5488 = injectiveMoment H raw5488step0 := by
      have heq : raw5488step0 = raw5488.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5488).symm
    injectiveMoment H raw5488step0 = injectiveMoment H raw5488step1 := by
      have heq : raw5488step1 = (fun i j => raw5488step0 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5488step0 permutation16 permutation1
    _ = injectiveMoment H node24 := by rfl

def raw5489 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical5489 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5489 = injectiveMoment H node241 := by
  rfl

def raw5490 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical5490 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5490 = injectiveMoment H node737 := by
  rfl

def raw5491 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical5491 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5491 = injectiveMoment H node739 := by
  rfl

def raw5492 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical5492 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5492 = injectiveMoment H node243 := by
  rfl

def raw5493 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

theorem canonical5493 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5493 = injectiveMoment H node244 := by
  rfl

def raw5494 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical5494 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5494 = injectiveMoment H node741 := by
  rfl

def raw5495 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical5495 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5495 = injectiveMoment H node742 := by
  rfl

def raw5496 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5496 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5496 = injectiveMoment H node743 := by
  rfl

def raw5497 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 2, -2], ![2, -1, -1]]

def raw5497step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![0, -2, 2], ![-2, 1, 1]]

def raw5497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

theorem canonical5497 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5497 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw5497 = injectiveMoment H raw5497step0 := by
      have heq : raw5497step0 = -raw5497 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5497).symm
    injectiveMoment H raw5497step0 = injectiveMoment H raw5497step1 := by
      have heq : raw5497step1 = (fun i j => raw5497step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5497step0 permutation32 permutation3
    _ = injectiveMoment H node225 := by rfl

def raw5498 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical5498 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5498 = injectiveMoment H node245 := by
  rfl

def raw5499 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical5499 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5499 = injectiveMoment H node246 := by
  rfl

def raw5500 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1]]

def raw5500step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical5500 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5500 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw5500 = injectiveMoment H raw5500step0 := by
      have heq : raw5500step0 = (fun i j => raw5500 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5500 permutation10 permutation3
    _ = injectiveMoment H node246 := by rfl

def raw5501 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![2, 1, -3]]

def raw5501step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, -1, 3]]

def raw5501step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

theorem canonical5501 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5501 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw5501 = injectiveMoment H raw5501step0 := by
      have heq : raw5501step0 = -raw5501 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5501).symm
    injectiveMoment H raw5501step0 = injectiveMoment H raw5501step1 := by
      have heq : raw5501step1 = (fun i j => raw5501step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5501step0 permutation8 permutation3
    _ = injectiveMoment H node40 := by rfl

def raw5502 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def raw5502step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical5502 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5502 = injectiveMoment H node248 := by
  calc
    injectiveMoment H raw5502 = injectiveMoment H raw5502step0 := by
      have hz : ∀ j, raw5502 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5502step0 = (fun i j => raw5502 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5502 permutation80 hz
    _ = injectiveMoment H node248 := by rfl

def raw5503 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5503 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5503 = injectiveMoment H node744 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
