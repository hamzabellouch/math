import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7520 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-3, 3, -1, 1], ![4, -3, -1, 0]]

def raw7520step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![2, -1, -1], ![-1, 1, 0]]

def raw7520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -3, 3], ![-2, 1, 1], ![1, -1, 0]]

def raw7520step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

theorem canonical7520 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7520 = injectiveMoment H node221 := by
  calc
    injectiveMoment H raw7520 = injectiveMoment H raw7520step0 := by
      have heq : raw7520step0 = raw7520.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7520).symm
    injectiveMoment H raw7520step0 = injectiveMoment H raw7520step1 := by
      have heq : raw7520step1 = -raw7520step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7520step0).symm
    injectiveMoment H raw7520step1 = injectiveMoment H raw7520step2 := by
      have heq : raw7520step2 = (fun i j => raw7520step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7520step1 permutation24 permutation3
    _ = injectiveMoment H node221 := by rfl

def raw7521 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-3, 3, 0, 0], ![4, -3, -2, 1]]

def raw7521step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 3, -3], ![2, 0, -2], ![-1, 0, 1]]

def raw7521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -3, 3], ![-2, 0, 2], ![1, 0, -1]]

def raw7521step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 0, -1], ![1, 3, -4]]

theorem canonical7521 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7521 = injectiveMoment H node195 := by
  calc
    injectiveMoment H raw7521 = injectiveMoment H raw7521step0 := by
      have heq : raw7521step0 = raw7521.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7521).symm
    injectiveMoment H raw7521step0 = injectiveMoment H raw7521step1 := by
      have heq : raw7521step1 = -raw7521step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7521step0).symm
    injectiveMoment H raw7521step1 = injectiveMoment H raw7521step2 := by
      have heq : raw7521step2 = (fun i j => raw7521step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7521step1 permutation24 permutation3
    _ = injectiveMoment H node195 := by rfl

def raw7522 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-2, 2, -2, 2], ![3, -2, 0, -1]]

def raw7522step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![2, -2, 0], ![-1, 2, -1]]

def raw7522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -2, 2], ![-2, 2, 0], ![1, -2, 1]]

def raw7522step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical7522 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7522 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw7522 = injectiveMoment H raw7522step0 := by
      have heq : raw7522step0 = raw7522.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7522).symm
    injectiveMoment H raw7522step0 = injectiveMoment H raw7522step1 := by
      have heq : raw7522step1 = -raw7522step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7522step0).symm
    injectiveMoment H raw7522step1 = injectiveMoment H raw7522step2 := by
      have heq : raw7522step2 = (fun i j => raw7522step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7522step1 permutation23 permutation4
    _ = injectiveMoment H node212 := by rfl

def raw7523 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-2, 2, -1, 1], ![3, -2, -1, 0]]

def raw7523step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![2, -1, -1], ![-1, 1, 0]]

def raw7523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -2, 2], ![-2, 1, 1], ![1, -1, 0]]

def raw7523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical7523 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7523 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw7523 = injectiveMoment H raw7523step0 := by
      have heq : raw7523step0 = raw7523.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7523).symm
    injectiveMoment H raw7523step0 = injectiveMoment H raw7523step1 := by
      have heq : raw7523step1 = -raw7523step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7523step0).symm
    injectiveMoment H raw7523step1 = injectiveMoment H raw7523step2 := by
      have heq : raw7523step2 = (fun i j => raw7523step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7523step1 permutation24 permutation3
    _ = injectiveMoment H node226 := by rfl

def raw7524 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-2, 2, 0, 0], ![3, -2, -2, 1]]

def raw7524step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![2, 0, -2], ![-1, 0, 1]]

def raw7524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical7524 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7524 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw7524 = injectiveMoment H raw7524step0 := by
      have heq : raw7524step0 = raw7524.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7524).symm
    injectiveMoment H raw7524step0 = injectiveMoment H raw7524step1 := by
      have heq : raw7524step1 = (fun i j => raw7524step0 (permutation14 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7524step0 permutation14 permutation5
    _ = injectiveMoment H node169 := by rfl

def raw7525 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-2, 3, -1, 0], ![3, -3, -1, 1]]

def raw7525step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![2, -1, -1], ![-1, 0, 1]]

def raw7525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -3, 3], ![-2, 1, 1], ![1, 0, -1]]

def raw7525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

theorem canonical7525 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7525 = injectiveMoment H node222 := by
  calc
    injectiveMoment H raw7525 = injectiveMoment H raw7525step0 := by
      have heq : raw7525step0 = raw7525.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7525).symm
    injectiveMoment H raw7525step0 = injectiveMoment H raw7525step1 := by
      have heq : raw7525step1 = -raw7525step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7525step0).symm
    injectiveMoment H raw7525step1 = injectiveMoment H raw7525step2 := by
      have heq : raw7525step2 = (fun i j => raw7525step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7525step1 permutation24 permutation3
    _ = injectiveMoment H node222 := by rfl

def raw7526 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-2, 4, -2, 0], ![3, -4, 0, 1]]

def raw7526step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![2, -2, 0], ![-1, 0, 1]]

def raw7526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -4, 4], ![-2, 2, 0], ![1, 0, -1]]

def raw7526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, -1, 0]]

theorem canonical7526 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7526 = injectiveMoment H node217 := by
  calc
    injectiveMoment H raw7526 = injectiveMoment H raw7526step0 := by
      have heq : raw7526step0 = raw7526.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7526).symm
    injectiveMoment H raw7526step0 = injectiveMoment H raw7526step1 := by
      have heq : raw7526step1 = -raw7526step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7526step0).symm
    injectiveMoment H raw7526step1 = injectiveMoment H raw7526step2 := by
      have heq : raw7526step2 = (fun i j => raw7526step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7526step1 permutation23 permutation4
    _ = injectiveMoment H node217 := by rfl

def raw7527 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -3, 0, 4], ![2, 3, -2, -3]]

def raw7527step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![2, 0, -2], ![-1, 4, -3]]

def raw7527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 3, -3], ![-2, 0, 2], ![1, -4, 3]]

def raw7527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]

theorem canonical7527 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7527 = injectiveMoment H node213 := by
  calc
    injectiveMoment H raw7527 = injectiveMoment H raw7527step0 := by
      have heq : raw7527step0 = raw7527.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7527).symm
    injectiveMoment H raw7527step0 = injectiveMoment H raw7527step1 := by
      have heq : raw7527step1 = -raw7527step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7527step0).symm
    injectiveMoment H raw7527step1 = injectiveMoment H raw7527step2 := by
      have heq : raw7527step2 = (fun i j => raw7527step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7527step1 permutation24 permutation3
    _ = injectiveMoment H node213 := by rfl

def raw7528 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -3, 2, 2], ![2, 3, -4, -1]]

def raw7528step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![2, 2, -4], ![-1, 2, -1]]

def raw7528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 3, -3], ![-2, -2, 4], ![1, -2, 1]]

def raw7528step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]

theorem canonical7528 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7528 = injectiveMoment H node154 := by
  calc
    injectiveMoment H raw7528 = injectiveMoment H raw7528step0 := by
      have heq : raw7528step0 = raw7528.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7528).symm
    injectiveMoment H raw7528step0 = injectiveMoment H raw7528step1 := by
      have heq : raw7528step1 = -raw7528step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7528step0).symm
    injectiveMoment H raw7528step1 = injectiveMoment H raw7528step2 := by
      have heq : raw7528step2 = (fun i j => raw7528step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7528step1 permutation24 permutation3
    _ = injectiveMoment H node154 := by rfl

def raw7529 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -2, -2, 5], ![2, 2, 0, -4]]

def raw7529step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![2, -2, 0], ![-1, 5, -4]]

def raw7529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, 2, 0], ![1, -5, 4]]

def raw7529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

theorem canonical7529 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7529 = injectiveMoment H node200 := by
  calc
    injectiveMoment H raw7529 = injectiveMoment H raw7529step0 := by
      have heq : raw7529step0 = raw7529.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7529).symm
    injectiveMoment H raw7529step0 = injectiveMoment H raw7529step1 := by
      have heq : raw7529step1 = -raw7529step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7529step0).symm
    injectiveMoment H raw7529step1 = injectiveMoment H raw7529step2 := by
      have heq : raw7529step2 = (fun i j => raw7529step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7529step1 permutation23 permutation4
    _ = injectiveMoment H node200 := by rfl

def raw7530 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -2, -1, 4], ![2, 2, -1, -3]]

def raw7530step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![2, -1, -1], ![-1, 4, -3]]

def raw7530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, 1, 1], ![1, -4, 3]]

def raw7530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

theorem canonical7530 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7530 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw7530 = injectiveMoment H raw7530step0 := by
      have heq : raw7530step0 = raw7530.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7530).symm
    injectiveMoment H raw7530step0 = injectiveMoment H raw7530step1 := by
      have heq : raw7530step1 = -raw7530step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7530step0).symm
    injectiveMoment H raw7530step1 = injectiveMoment H raw7530step2 := by
      have heq : raw7530step2 = (fun i j => raw7530step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7530step1 permutation23 permutation4
    _ = injectiveMoment H node225 := by rfl

def raw7531 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -2, 0, 3], ![2, 2, -2, -2]]

def raw7531step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![2, 0, -2], ![-1, 3, -2]]

def raw7531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, 0, 2], ![1, -3, 2]]

def raw7531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical7531 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7531 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw7531 = injectiveMoment H raw7531step0 := by
      have heq : raw7531step0 = raw7531.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7531).symm
    injectiveMoment H raw7531step0 = injectiveMoment H raw7531step1 := by
      have heq : raw7531step1 = -raw7531step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7531step0).symm
    injectiveMoment H raw7531step1 = injectiveMoment H raw7531step2 := by
      have heq : raw7531step2 = (fun i j => raw7531step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7531step1 permutation24 permutation3
    _ = injectiveMoment H node212 := by rfl

def raw7532 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -2, 1, 2], ![2, 2, -3, -1]]

def raw7532step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![2, 1, -3], ![-1, 2, -1]]

def raw7532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, -1, 3], ![1, -2, 1]]

def raw7532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical7532 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7532 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw7532 = injectiveMoment H raw7532step0 := by
      have heq : raw7532step0 = raw7532.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7532).symm
    injectiveMoment H raw7532step0 = injectiveMoment H raw7532step1 := by
      have heq : raw7532step1 = -raw7532step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7532step0).symm
    injectiveMoment H raw7532step1 = injectiveMoment H raw7532step2 := by
      have heq : raw7532step2 = (fun i j => raw7532step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7532step1 permutation24 permutation3
    _ = injectiveMoment H node184 := by rfl

def raw7533 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -2, 2, 1], ![2, 2, -4, 0]]

def raw7533step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![2, 2, -4], ![-1, 1, 0]]

def raw7533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, -2, 4], ![1, -1, 0]]

def raw7533step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7533 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7533 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw7533 = injectiveMoment H raw7533step0 := by
      have heq : raw7533step0 = raw7533.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7533).symm
    injectiveMoment H raw7533step0 = injectiveMoment H raw7533step1 := by
      have heq : raw7533step1 = -raw7533step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7533step0).symm
    injectiveMoment H raw7533step1 = injectiveMoment H raw7533step2 := by
      have heq : raw7533step2 = (fun i j => raw7533step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7533step1 permutation24 permutation3
    _ = injectiveMoment H node153 := by rfl

def raw7534 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, -2, 3, 0], ![2, 2, -5, 1]]

def raw7534step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![2, 3, -5], ![-1, 0, 1]]

def raw7534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, -3, 5], ![1, 0, -1]]

def raw7534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical7534 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7534 = injectiveMoment H node127 := by
  calc
    injectiveMoment H raw7534 = injectiveMoment H raw7534step0 := by
      have heq : raw7534step0 = raw7534.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7534).symm
    injectiveMoment H raw7534step0 = injectiveMoment H raw7534step1 := by
      have heq : raw7534step1 = -raw7534step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7534step0).symm
    injectiveMoment H raw7534step1 = injectiveMoment H raw7534step2 := by
      have heq : raw7534step2 = (fun i j => raw7534step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7534step1 permutation24 permutation3
    _ = injectiveMoment H node127 := by rfl

def raw7535 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 2, -4, 3], ![2, -2, 2, -2]]

def raw7535step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![2, -4, 2], ![-1, 3, -2]]

def raw7535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-2, 4, -2], ![1, -3, 2]]

def raw7535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

theorem canonical7535 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7535 = injectiveMoment H node152 := by
  calc
    injectiveMoment H raw7535 = injectiveMoment H raw7535step0 := by
      have heq : raw7535step0 = raw7535.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7535).symm
    injectiveMoment H raw7535step0 = injectiveMoment H raw7535step1 := by
      have heq : raw7535step1 = -raw7535step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7535step0).symm
    injectiveMoment H raw7535step1 = injectiveMoment H raw7535step2 := by
      have heq : raw7535step2 = (fun i j => raw7535step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7535step1 permutation23 permutation4
    _ = injectiveMoment H node152 := by rfl

def raw7536 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 2, -3, 2], ![2, -2, 1, -1]]

def raw7536step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![2, -3, 1], ![-1, 2, -1]]

def raw7536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-2, 3, -1], ![1, -2, 1]]

def raw7536step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical7536 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7536 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw7536 = injectiveMoment H raw7536step0 := by
      have heq : raw7536step0 = raw7536.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7536).symm
    injectiveMoment H raw7536step0 = injectiveMoment H raw7536step1 := by
      have heq : raw7536step1 = -raw7536step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7536step0).symm
    injectiveMoment H raw7536step1 = injectiveMoment H raw7536step2 := by
      have heq : raw7536step2 = (fun i j => raw7536step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7536step1 permutation23 permutation4
    _ = injectiveMoment H node184 := by rfl

def raw7537 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 2, -2, 1], ![2, -2, 0, 0]]

def raw7537step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![-1, 1, 0]]

def raw7537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical7537 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7537 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw7537 = injectiveMoment H raw7537step0 := by
      have heq : raw7537step0 = raw7537.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7537).symm
    injectiveMoment H raw7537step0 = injectiveMoment H raw7537step1 := by
      have heq : raw7537step1 = (fun i j => raw7537step0 (permutation20 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7537step0 permutation20 permutation7
    _ = injectiveMoment H node203 := by rfl

def raw7538 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 2, -1, 0], ![2, -2, -1, 1]]

def raw7538step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![-1, 0, 1]]

def raw7538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-2, 1, 1], ![1, 0, -1]]

def raw7538step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical7538 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7538 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw7538 = injectiveMoment H raw7538step0 := by
      have heq : raw7538step0 = raw7538.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7538).symm
    injectiveMoment H raw7538step0 = injectiveMoment H raw7538step1 := by
      have heq : raw7538step1 = -raw7538step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7538step0).symm
    injectiveMoment H raw7538step1 = injectiveMoment H raw7538step2 := by
      have heq : raw7538step2 = (fun i j => raw7538step1 (permutation20 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7538step1 permutation20 permutation5
    _ = injectiveMoment H node210 := by rfl

def raw7539 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 2, 0, -1], ![2, -2, -2, 2]]

def raw7539step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![2, 0, -2], ![-1, -1, 2]]

def raw7539step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-2, 0, 2], ![1, 1, -2]]

def raw7539step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

theorem canonical7539 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7539 = injectiveMoment H node202 := by
  calc
    injectiveMoment H raw7539 = injectiveMoment H raw7539step0 := by
      have heq : raw7539step0 = raw7539.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7539).symm
    injectiveMoment H raw7539step0 = injectiveMoment H raw7539step1 := by
      have heq : raw7539step1 = -raw7539step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7539step0).symm
    injectiveMoment H raw7539step1 = injectiveMoment H raw7539step2 := by
      have heq : raw7539step2 = (fun i j => raw7539step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7539step1 permutation23 permutation3
    _ = injectiveMoment H node202 := by rfl

def raw7540 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 2, 1, -2], ![2, -2, -3, 3]]

def raw7540step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![2, 1, -3], ![-1, -2, 3]]

def raw7540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -2, 2], ![-2, -1, 3], ![1, 2, -3]]

def raw7540step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical7540 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7540 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw7540 = injectiveMoment H raw7540step0 := by
      have heq : raw7540step0 = raw7540.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7540).symm
    injectiveMoment H raw7540step0 = injectiveMoment H raw7540step1 := by
      have heq : raw7540step1 = -raw7540step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7540step0).symm
    injectiveMoment H raw7540step1 = injectiveMoment H raw7540step2 := by
      have heq : raw7540step2 = (fun i j => raw7540step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7540step1 permutation23 permutation3
    _ = injectiveMoment H node167 := by rfl

def raw7541 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 3, -4, 2], ![2, -3, 2, -1]]

def raw7541step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![2, -4, 2], ![-1, 2, -1]]

def raw7541step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![-2, 4, -2], ![1, -2, 1]]

def raw7541step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]

theorem canonical7541 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7541 = injectiveMoment H node154 := by
  calc
    injectiveMoment H raw7541 = injectiveMoment H raw7541step0 := by
      have heq : raw7541step0 = raw7541.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7541).symm
    injectiveMoment H raw7541step0 = injectiveMoment H raw7541step1 := by
      have heq : raw7541step1 = -raw7541step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7541step0).symm
    injectiveMoment H raw7541step1 = injectiveMoment H raw7541step2 := by
      have heq : raw7541step2 = (fun i j => raw7541step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7541step1 permutation23 permutation4
    _ = injectiveMoment H node154 := by rfl

def raw7542 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 3, -2, 0], ![2, -3, 0, 1]]

def raw7542step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![2, -2, 0], ![-1, 0, 1]]

def raw7542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![-2, 2, 0], ![1, 0, -1]]

def raw7542step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical7542 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7542 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw7542 = injectiveMoment H raw7542step0 := by
      have heq : raw7542step0 = raw7542.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7542).symm
    injectiveMoment H raw7542step0 = injectiveMoment H raw7542step1 := by
      have heq : raw7542step1 = -raw7542step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7542step0).symm
    injectiveMoment H raw7542step1 = injectiveMoment H raw7542step2 := by
      have heq : raw7542step2 = (fun i j => raw7542step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7542step1 permutation23 permutation4
    _ = injectiveMoment H node215 := by rfl

def raw7543 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 3, -1, -1], ![2, -3, -1, 2]]

def raw7543step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![2, -1, -1], ![-1, -1, 2]]

def raw7543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![-2, 1, 1], ![1, 1, -2]]

def raw7543step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

theorem canonical7543 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7543 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw7543 = injectiveMoment H raw7543step0 := by
      have heq : raw7543step0 = raw7543.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7543).symm
    injectiveMoment H raw7543step0 = injectiveMoment H raw7543step1 := by
      have heq : raw7543step1 = -raw7543step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7543step0).symm
    injectiveMoment H raw7543step1 = injectiveMoment H raw7543step2 := by
      have heq : raw7543step2 = (fun i j => raw7543step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7543step1 permutation23 permutation3
    _ = injectiveMoment H node223 := by rfl

def raw7544 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 3, 0, -2], ![2, -3, -2, 3]]

def raw7544step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![2, 0, -2], ![-1, -2, 3]]

def raw7544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -3, 3], ![-2, 0, 2], ![1, 2, -3]]

def raw7544step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

theorem canonical7544 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7544 = injectiveMoment H node196 := by
  calc
    injectiveMoment H raw7544 = injectiveMoment H raw7544step0 := by
      have heq : raw7544step0 = raw7544.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7544).symm
    injectiveMoment H raw7544step0 = injectiveMoment H raw7544step1 := by
      have heq : raw7544step1 = -raw7544step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7544step0).symm
    injectiveMoment H raw7544step1 = injectiveMoment H raw7544step2 := by
      have heq : raw7544step2 = (fun i j => raw7544step1 (permutation23 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7544step1 permutation23 permutation3
    _ = injectiveMoment H node196 := by rfl

def raw7545 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![-1, 4, -3, 0], ![2, -4, 1, 1]]

def raw7545step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 4, -4], ![2, -3, 1], ![-1, 0, 1]]

def raw7545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, -4, 4], ![-2, 3, -1], ![1, 0, -1]]

def raw7545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

theorem canonical7545 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7545 = injectiveMoment H node190 := by
  calc
    injectiveMoment H raw7545 = injectiveMoment H raw7545step0 := by
      have heq : raw7545step0 = raw7545.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7545).symm
    injectiveMoment H raw7545step0 = injectiveMoment H raw7545step1 := by
      have heq : raw7545step1 = -raw7545step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7545step0).symm
    injectiveMoment H raw7545step1 = injectiveMoment H raw7545step2 := by
      have heq : raw7545step2 = (fun i j => raw7545step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7545step1 permutation23 permutation4
    _ = injectiveMoment H node190 := by rfl

def raw7546 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -3, 0, 3], ![1, 3, -2, -2]]

def raw7546step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![2, 0, -2], ![-1, 3, -2]]

def raw7546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-2, 0, 2], ![1, -3, 2]]

def raw7546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical7546 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7546 = injectiveMoment H node214 := by
  calc
    injectiveMoment H raw7546 = injectiveMoment H raw7546step0 := by
      have heq : raw7546step0 = raw7546.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7546).symm
    injectiveMoment H raw7546step0 = injectiveMoment H raw7546step1 := by
      have heq : raw7546step1 = -raw7546step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7546step0).symm
    injectiveMoment H raw7546step1 = injectiveMoment H raw7546step2 := by
      have heq : raw7546step2 = (fun i j => raw7546step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7546step1 permutation24 permutation3
    _ = injectiveMoment H node214 := by rfl

def raw7547 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -3, 1, 2], ![1, 3, -3, -1]]

def raw7547step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![2, 1, -3], ![-1, 2, -1]]

def raw7547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-2, -1, 3], ![1, -2, 1]]

def raw7547step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical7547 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7547 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw7547 = injectiveMoment H raw7547step0 := by
      have heq : raw7547step0 = raw7547.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7547).symm
    injectiveMoment H raw7547step0 = injectiveMoment H raw7547step1 := by
      have heq : raw7547step1 = -raw7547step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7547step0).symm
    injectiveMoment H raw7547step1 = injectiveMoment H raw7547step2 := by
      have heq : raw7547step2 = (fun i j => raw7547step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7547step1 permutation24 permutation3
    _ = injectiveMoment H node187 := by rfl

def raw7548 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -3, 2, 1], ![1, 3, -4, 0]]

def raw7548step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![2, 2, -4], ![-1, 1, 0]]

def raw7548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 3, -3], ![-2, -2, 4], ![1, -1, 0]]

def raw7548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7548 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7548 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw7548 = injectiveMoment H raw7548step0 := by
      have heq : raw7548step0 = raw7548.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7548).symm
    injectiveMoment H raw7548step0 = injectiveMoment H raw7548step1 := by
      have heq : raw7548step1 = -raw7548step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7548step0).symm
    injectiveMoment H raw7548step1 = injectiveMoment H raw7548step2 := by
      have heq : raw7548step2 = (fun i j => raw7548step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7548step1 permutation24 permutation3
    _ = injectiveMoment H node155 := by rfl

def raw7549 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, -2, 4], ![1, 2, 0, -3]]

def raw7549step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![2, -2, 0], ![-1, 4, -3]]

def raw7549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-2, 2, 0], ![1, -4, 3]]

def raw7549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical7549 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7549 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw7549 = injectiveMoment H raw7549step0 := by
      have heq : raw7549step0 = raw7549.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7549).symm
    injectiveMoment H raw7549step0 = injectiveMoment H raw7549step1 := by
      have heq : raw7549step1 = -raw7549step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7549step0).symm
    injectiveMoment H raw7549step1 = injectiveMoment H raw7549step2 := by
      have heq : raw7549step2 = (fun i j => raw7549step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7549step1 permutation23 permutation4
    _ = injectiveMoment H node201 := by rfl

def raw7550 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, -1, 3], ![1, 2, -1, -2]]

def raw7550step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![-1, 3, -2]]

def raw7550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![-2, 1, 1], ![1, -3, 2]]

def raw7550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical7550 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7550 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw7550 = injectiveMoment H raw7550step0 := by
      have heq : raw7550step0 = raw7550.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7550).symm
    injectiveMoment H raw7550step0 = injectiveMoment H raw7550step1 := by
      have heq : raw7550step1 = -raw7550step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7550step0).symm
    injectiveMoment H raw7550step1 = injectiveMoment H raw7550step2 := by
      have heq : raw7550step2 = (fun i j => raw7550step1 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7550step1 permutation23 permutation4
    _ = injectiveMoment H node226 := by rfl

def raw7551 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def raw7551step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical7551 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7551 = injectiveMoment H node1002 := by
  calc
    injectiveMoment H raw7551 = injectiveMoment H raw7551step0 := by
      have heq : raw7551step0 = (fun i j => raw7551 (permutation11 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7551 permutation11 permutation13
    _ = injectiveMoment H node1002 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
