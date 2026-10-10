import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8704 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def raw8704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def raw8704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical8704 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8704 = injectiveMoment H node883 := by
  calc
    injectiveMoment H raw8704 = injectiveMoment H raw8704step0 := by
      have hz : ∀ j, raw8704 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8704step0 = (fun i j => raw8704 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8704 permutation221 hz
    injectiveMoment H raw8704step0 = injectiveMoment H raw8704step1 := by
      have heq : raw8704step1 = (fun i j => raw8704step0 (permutation111 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8704step0 permutation111 permutation4
    _ = injectiveMoment H node883 := by rfl

def raw8705 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def raw8705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def raw8705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8705 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8705 = injectiveMoment H node1291 := by
  calc
    injectiveMoment H raw8705 = injectiveMoment H raw8705step0 := by
      have hz : ∀ j, raw8705 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8705step0 = (fun i j => raw8705 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8705 permutation221 hz
    injectiveMoment H raw8705step0 = injectiveMoment H raw8705step1 := by
      have heq : raw8705step1 = (fun i j => raw8705step0 (permutation54 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8705step0 permutation54 permutation5
    _ = injectiveMoment H node1291 := by rfl

def raw8706 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def raw8706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def raw8706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical8706 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8706 = injectiveMoment H node560 := by
  calc
    injectiveMoment H raw8706 = injectiveMoment H raw8706step0 := by
      have hz : ∀ j, raw8706 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8706step0 = (fun i j => raw8706 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8706 permutation221 hz
    injectiveMoment H raw8706step0 = injectiveMoment H raw8706step1 := by
      have heq : raw8706step1 = (fun i j => raw8706step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8706step0 permutation128 permutation3
    _ = injectiveMoment H node560 := by rfl

def raw8707 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![-3, 1, 2]]

def raw8707step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![3, -1, -2]]

def raw8707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![3, -1, -2]]

def raw8707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8707 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8707 = injectiveMoment H node868 := by
  calc
    injectiveMoment H raw8707 = injectiveMoment H raw8707step0 := by
      have heq : raw8707step0 = -raw8707 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8707).symm
    injectiveMoment H raw8707step0 = injectiveMoment H raw8707step1 := by
      have hz : ∀ j, raw8707step0 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw8707step1 = (fun i j => raw8707step0 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8707step0 permutation221 hz
    injectiveMoment H raw8707step1 = injectiveMoment H raw8707step2 := by
      have heq : raw8707step2 = (fun i j => raw8707step1 (permutation135 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8707step1 permutation135 permutation6
    _ = injectiveMoment H node868 := by rfl

def raw8708 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![-1, -1, 2], ![3, 0, -3]]

def raw8708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8708 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8708 = injectiveMoment H node2654 := by
  calc
    injectiveMoment H raw8708 = injectiveMoment H raw8708step0 := by
      have heq : raw8708step0 = (fun i j => raw8708 (permutation274 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8708 permutation274 permutation5
    _ = injectiveMoment H node2654 := by rfl

def raw8709 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-1, -2, 3], ![3, 0, -3]]

def raw8709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 2, -3], ![-3, 0, 3]]

def raw8709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

theorem canonical8709 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8709 = injectiveMoment H node1400 := by
  calc
    injectiveMoment H raw8709 = injectiveMoment H raw8709step0 := by
      have heq : raw8709step0 = -raw8709 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8709).symm
    injectiveMoment H raw8709step0 = injectiveMoment H raw8709step1 := by
      have heq : raw8709step1 = (fun i j => raw8709step0 (permutation338 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8709step0 permutation338 permutation3
    _ = injectiveMoment H node1400 := by rfl

def raw8710 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, -1, -2]]

def raw8710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2], ![-3, 1, 2]]

def raw8710step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical8710 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8710 = injectiveMoment H node1423 := by
  calc
    injectiveMoment H raw8710 = injectiveMoment H raw8710step0 := by
      have heq : raw8710step0 = -raw8710 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8710).symm
    injectiveMoment H raw8710step0 = injectiveMoment H raw8710step1 := by
      have heq : raw8710step1 = (fun i j => raw8710step0 (permutation338 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8710step0 permutation338 permutation3
    _ = injectiveMoment H node1423 := by rfl

def raw8711 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1]]

def raw8711step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![1, -1], ![-1, 1]]

def raw8711step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical8711 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8711 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw8711 = injectiveMoment H raw8711step0 := by
      have hz : ∀ i, raw8711 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8711step0 = (fun i j => raw8711 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8711 permutation3 hz
    injectiveMoment H raw8711step0 = injectiveMoment H raw8711step1 := by
      have heq : raw8711step1 = (fun i j => raw8711step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8711step0 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

def raw8712 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-2, -1, 3], ![2, 1, -3]]

def raw8712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical8712 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8712 = injectiveMoment H node1873 := by
  calc
    injectiveMoment H raw8712 = injectiveMoment H raw8712step0 := by
      have heq : raw8712step0 = (fun i j => raw8712 (permutation270 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8712 permutation270 permutation3
    _ = injectiveMoment H node1873 := by rfl

def raw8713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![1, 2, -3]]

def raw8713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]

theorem canonical8713 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8713 = injectiveMoment H node2476 := by
  calc
    injectiveMoment H raw8713 = injectiveMoment H raw8713step0 := by
      have heq : raw8713step0 = (fun i j => raw8713 (permutation270 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8713 permutation270 permutation3
    _ = injectiveMoment H node2476 := by rfl

def raw8714 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![-1, -1, 2]]

def raw8714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![-1, -1, 2]]

def raw8714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8714 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8714 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H raw8714 = injectiveMoment H raw8714step0 := by
      have hz : ∀ j, raw8714 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw8714step0 = (fun i j => raw8714 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8714 permutation241 hz
    injectiveMoment H raw8714step0 = injectiveMoment H raw8714step1 := by
      have heq : raw8714step1 = (fun i j => raw8714step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8714step0 permutation128 permutation3
    _ = injectiveMoment H node1151 := by rfl

def raw8715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![-3, 0, 3], ![2, 1, -3]]

def raw8715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

theorem canonical8715 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8715 = injectiveMoment H node1403 := by
  calc
    injectiveMoment H raw8715 = injectiveMoment H raw8715step0 := by
      have heq : raw8715step0 = (fun i j => raw8715 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8715 permutation258 permutation3
    _ = injectiveMoment H node1403 := by rfl

def raw8716 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![-2, -1, 3], ![1, 2, -3]]

def raw8716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical8716 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8716 = injectiveMoment H node1882 := by
  calc
    injectiveMoment H raw8716 = injectiveMoment H raw8716step0 := by
      have heq : raw8716step0 = (fun i j => raw8716 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8716 permutation258 permutation3
    _ = injectiveMoment H node1882 := by rfl

def raw8717 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![-2, 1, 1]]

def raw8717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8717 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8717 = injectiveMoment H node2305 := by
  calc
    injectiveMoment H raw8717 = injectiveMoment H raw8717step0 := by
      have heq : raw8717step0 = (fun i j => raw8717 (permutation338 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8717 permutation338 permutation4
    _ = injectiveMoment H node2305 := by rfl

def raw8718 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2], ![-3, 1, 2]]

def raw8718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

theorem canonical8718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8718 = injectiveMoment H node1426 := by
  calc
    injectiveMoment H raw8718 = injectiveMoment H raw8718step0 := by
      have heq : raw8718step0 = (fun i j => raw8718 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8718 permutation308 permutation3
    _ = injectiveMoment H node1426 := by rfl

def raw8719 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-3, -1, 4], ![2, 1, -3]]

def raw8719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

theorem canonical8719 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8719 = injectiveMoment H node1383 := by
  calc
    injectiveMoment H raw8719 = injectiveMoment H raw8719step0 := by
      have heq : raw8719step0 = (fun i j => raw8719 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8719 permutation258 permutation3
    _ = injectiveMoment H node1383 := by rfl

def raw8720 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-3, 0, 3], ![2, 0, -2]]

def raw8720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![3, 0, -3], ![-2, 0, 2]]

def raw8720step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8720 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8720 = injectiveMoment H node2788 := by
  calc
    injectiveMoment H raw8720 = injectiveMoment H raw8720step0 := by
      have heq : raw8720step0 = -raw8720 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8720).symm
    injectiveMoment H raw8720step0 = injectiveMoment H raw8720step1 := by
      have heq : raw8720step1 = (fun i j => raw8720step0 (permutation211 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8720step0 permutation211 permutation5
    _ = injectiveMoment H node2788 := by rfl

def raw8721 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -2, 4], ![1, 2, -3]]

def raw8721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical8721 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8721 = injectiveMoment H node1537 := by
  calc
    injectiveMoment H raw8721 = injectiveMoment H raw8721step0 := by
      have heq : raw8721step0 = (fun i j => raw8721 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8721 permutation258 permutation3
    _ = injectiveMoment H node1537 := by rfl

def raw8722 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 1, -2]]

def raw8722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8722 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8722 = injectiveMoment H node1883 := by
  calc
    injectiveMoment H raw8722 = injectiveMoment H raw8722step0 := by
      have heq : raw8722step0 = (fun i j => raw8722 (permutation258 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8722 permutation258 permutation3
    _ = injectiveMoment H node1883 := by rfl

def raw8723 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3], ![0, 2, -2]]

def raw8723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical8723 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8723 = injectiveMoment H node2479 := by
  calc
    injectiveMoment H raw8723 = injectiveMoment H raw8723step0 := by
      have heq : raw8723step0 = (fun i j => raw8723 (permutation259 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8723 permutation259 permutation3
    _ = injectiveMoment H node2479 := by rfl

def raw8724 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1]]

def raw8724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8724 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8724 = injectiveMoment H node2306 := by
  calc
    injectiveMoment H raw8724 = injectiveMoment H raw8724step0 := by
      have heq : raw8724step0 = (fun i j => raw8724 (permutation337 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8724 permutation337 permutation4
    _ = injectiveMoment H node2306 := by rfl

def raw8725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2]]

def raw8725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8725 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8725 = injectiveMoment H node2137 := by
  calc
    injectiveMoment H raw8725 = injectiveMoment H raw8725step0 := by
      have heq : raw8725step0 = (fun i j => raw8725 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8725 permutation308 permutation3
    _ = injectiveMoment H node2137 := by rfl

def raw8726 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -1, 3]]

def raw8726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8726 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8726 = injectiveMoment H node1883 := by
  calc
    injectiveMoment H raw8726 = injectiveMoment H raw8726step0 := by
      have heq : raw8726step0 = (fun i j => raw8726 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8726 permutation308 permutation3
    _ = injectiveMoment H node1883 := by rfl

def raw8727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, 1, 2]]

def raw8727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

theorem canonical8727 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8727 = injectiveMoment H node1427 := by
  calc
    injectiveMoment H raw8727 = injectiveMoment H raw8727step0 := by
      have heq : raw8727step0 = (fun i j => raw8727 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8727 permutation308 permutation3
    _ = injectiveMoment H node1427 := by rfl

def raw8728 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, 0, 3]]

def raw8728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2], ![3, 0, -3]]

def raw8728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8728 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8728 = injectiveMoment H node2788 := by
  calc
    injectiveMoment H raw8728 = injectiveMoment H raw8728step0 := by
      have heq : raw8728step0 = -raw8728 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8728).symm
    injectiveMoment H raw8728step0 = injectiveMoment H raw8728step1 := by
      have heq : raw8728step1 = (fun i j => raw8728step0 (permutation210 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8728step0 permutation210 permutation5
    _ = injectiveMoment H node2788 := by rfl

def raw8729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2]]

def raw8729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![-1, -1, 2]]

def raw8729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8729 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8729 = injectiveMoment H node1151 := by
  calc
    injectiveMoment H raw8729 = injectiveMoment H raw8729step0 := by
      have hz : ∀ j, raw8729 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw8729step0 = (fun i j => raw8729 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8729 permutation258 hz
    injectiveMoment H raw8729step0 = injectiveMoment H raw8729step1 := by
      have heq : raw8729step1 = (fun i j => raw8729step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8729step0 permutation128 permutation3
    _ = injectiveMoment H node1151 := by rfl

def raw8730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2]]

def raw8730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8730 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8730 = injectiveMoment H node2137 := by
  calc
    injectiveMoment H raw8730 = injectiveMoment H raw8730step0 := by
      have heq : raw8730step0 = (fun i j => raw8730 (permutation309 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8730 permutation309 permutation3
    _ = injectiveMoment H node2137 := by rfl

def raw8731 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -1, 3]]

def raw8731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical8731 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8731 = injectiveMoment H node1884 := by
  calc
    injectiveMoment H raw8731 = injectiveMoment H raw8731step0 := by
      have heq : raw8731step0 = (fun i j => raw8731 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8731 permutation308 permutation3
    _ = injectiveMoment H node1884 := by rfl

def raw8732 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![-2, -2, 4]]

def raw8732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical8732 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8732 = injectiveMoment H node1538 := by
  calc
    injectiveMoment H raw8732 = injectiveMoment H raw8732step0 := by
      have heq : raw8732step0 = (fun i j => raw8732 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8732 permutation308 permutation3
    _ = injectiveMoment H node1538 := by rfl

def raw8733 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, 1, 2]]

def raw8733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

theorem canonical8733 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8733 = injectiveMoment H node1428 := by
  calc
    injectiveMoment H raw8733 = injectiveMoment H raw8733step0 := by
      have heq : raw8733step0 = (fun i j => raw8733 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8733 permutation308 permutation3
    _ = injectiveMoment H node1428 := by rfl

def raw8734 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![-3, 0, 3]]

def raw8734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![3, 0, -3]]

def raw8734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical8734 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8734 = injectiveMoment H node2790 := by
  calc
    injectiveMoment H raw8734 = injectiveMoment H raw8734step0 := by
      have heq : raw8734step0 = -raw8734 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8734).symm
    injectiveMoment H raw8734step0 = injectiveMoment H raw8734step1 := by
      have heq : raw8734step1 = (fun i j => raw8734step0 (permutation208 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8734step0 permutation208 permutation5
    _ = injectiveMoment H node2790 := by rfl

def raw8735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![-2, 0, 2], ![0, 3, -3]]

def raw8735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical8735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8735 = injectiveMoment H node2140 := by
  calc
    injectiveMoment H raw8735 = injectiveMoment H raw8735step0 := by
      have heq : raw8735step0 = (fun i j => raw8735 (permutation262 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8735 permutation262 permutation3
    _ = injectiveMoment H node2140 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
