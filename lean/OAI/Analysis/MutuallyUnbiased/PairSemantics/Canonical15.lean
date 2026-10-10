import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw480 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]

def raw480step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-2, -2, 4]]

def raw480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

theorem canonical480 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw480 = injectiveMoment H node141 := by
  calc
    injectiveMoment H raw480 = injectiveMoment H raw480step0 := by
      have heq : raw480step0 = -raw480 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw480).symm
    injectiveMoment H raw480step0 = injectiveMoment H raw480step1 := by
      have heq : raw480step1 = (fun i j => raw480step0 (permutation31 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw480step0 permutation31 permutation5
    _ = injectiveMoment H node141 := by rfl

def raw481 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 1, -2]]

def raw481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical481 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw481 = injectiveMoment H node634 := by
  calc
    injectiveMoment H raw481 = injectiveMoment H raw481step0 := by
      have heq : raw481step0 = (fun i j => raw481 (permutation59 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw481 permutation59 permutation5
    _ = injectiveMoment H node634 := by rfl

def raw482 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]

def raw482step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

theorem canonical482 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw482 = injectiveMoment H node196 := by
  calc
    injectiveMoment H raw482 = injectiveMoment H raw482step0 := by
      have heq : raw482step0 = (fun i j => raw482 (permutation15 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw482 permutation15 permutation5
    _ = injectiveMoment H node196 := by rfl

def raw483 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, 0, -1]]

def raw483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -2, 3], ![-1, 0, 1], ![-1, 0, 1]]

def raw483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

theorem canonical483 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw483 = injectiveMoment H node551 := by
  calc
    injectiveMoment H raw483 = injectiveMoment H raw483step0 := by
      have heq : raw483step0 = -raw483 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw483).symm
    injectiveMoment H raw483step0 = injectiveMoment H raw483step1 := by
      have heq : raw483step1 = (fun i j => raw483step0 (permutation96 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw483step0 permutation96 permutation5
    _ = injectiveMoment H node551 := by rfl

def raw484 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]

def raw484step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -2, 3], ![-2, 0, 2]]

def raw484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

theorem canonical484 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw484 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw484 = injectiveMoment H raw484step0 := by
      have heq : raw484step0 = -raw484 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw484).symm
    injectiveMoment H raw484step0 = injectiveMoment H raw484step1 := by
      have heq : raw484step1 = (fun i j => raw484step0 (permutation25 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw484step0 permutation25 permutation5
    _ = injectiveMoment H node163 := by rfl

def raw485 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 3, -4], ![2, -1, -1]]

def raw485step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -3, 4], ![-2, 1, 1]]

def raw485step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

theorem canonical485 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw485 = injectiveMoment H node86 := by
  calc
    injectiveMoment H raw485 = injectiveMoment H raw485step0 := by
      have heq : raw485step0 = -raw485 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw485).symm
    injectiveMoment H raw485step0 = injectiveMoment H raw485step1 := by
      have heq : raw485step1 = (fun i j => raw485step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw485step0 permutation22 permutation5
    _ = injectiveMoment H node86 := by rfl

def raw486 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![2, 0, -2], ![1, 2, -3]]

def raw486step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-2, 0, 2], ![-1, -2, 3]]

def raw486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

theorem canonical486 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw486 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw486 = injectiveMoment H raw486step0 := by
      have heq : raw486step0 = -raw486 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw486).symm
    injectiveMoment H raw486step0 = injectiveMoment H raw486step1 := by
      have heq : raw486step1 = (fun i j => raw486step0 (permutation31 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw486step0 permutation31 permutation5
    _ = injectiveMoment H node163 := by rfl

def raw487 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]

def raw487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]

def raw487step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]

def raw487step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical487 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw487 = injectiveMoment H node214 := by
  calc
    injectiveMoment H raw487 = injectiveMoment H raw487step0 := by
      have heq : raw487step0 = -raw487 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw487).symm
    injectiveMoment H raw487step0 = injectiveMoment H raw487step1 := by
      have hz : ∀ j, raw487step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw487step1 = (fun i j => raw487step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw487step0 permutation80 hz
    injectiveMoment H raw487step1 = injectiveMoment H raw487step2 := by
      have heq : raw487step2 = (fun i j => raw487step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw487step1 permutation22 permutation5
    _ = injectiveMoment H node214 := by rfl

def raw488 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]

def raw488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]

def raw488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-2, -2, 4]]

def raw488step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical488 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw488 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw488 = injectiveMoment H raw488step0 := by
      have heq : raw488step0 = -raw488 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw488).symm
    injectiveMoment H raw488step0 = injectiveMoment H raw488step1 := by
      have hz : ∀ j, raw488step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw488step1 = (fun i j => raw488step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw488step0 permutation80 hz
    injectiveMoment H raw488step1 = injectiveMoment H raw488step2 := by
      have heq : raw488step2 = (fun i j => raw488step1 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw488step1 permutation28 permutation5
    _ = injectiveMoment H node155 := by rfl

def raw489 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]

def raw489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 0, 0], ![-1, -2, 3], ![-2, 1, 1]]

def raw489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]

def raw489step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical489 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw489 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw489 = injectiveMoment H raw489step0 := by
      have heq : raw489step0 = -raw489 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw489).symm
    injectiveMoment H raw489step0 = injectiveMoment H raw489step1 := by
      have hz : ∀ j, raw489step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw489step1 = (fun i j => raw489step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw489step0 permutation80 hz
    injectiveMoment H raw489step1 = injectiveMoment H raw489step2 := by
      have heq : raw489step2 = (fun i j => raw489step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw489step1 permutation22 permutation5
    _ = injectiveMoment H node187 := by rfl

def raw490 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]

def raw490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]

def raw490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical490 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw490 = injectiveMoment H node1287 := by
  calc
    injectiveMoment H raw490 = injectiveMoment H raw490step0 := by
      have heq : raw490step0 = -raw490 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw490).symm
    injectiveMoment H raw490step0 = injectiveMoment H raw490step1 := by
      have heq : raw490step1 = (fun i j => raw490step0 (permutation93 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw490step0 permutation93 permutation5
    _ = injectiveMoment H node1287 := by rfl

def raw491 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

theorem canonical491 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw491 = injectiveMoment H node334 := by
  rfl

def raw492 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]

theorem canonical492 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw492 = injectiveMoment H node335 := by
  rfl

def raw493 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]

def raw493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical493 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw493 = injectiveMoment H node864 := by
  calc
    injectiveMoment H raw493 = injectiveMoment H raw493step0 := by
      have heq : raw493step0 = -raw493 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw493).symm
    injectiveMoment H raw493step0 = injectiveMoment H raw493step1 := by
      have heq : raw493step1 = (fun i j => raw493step0 (permutation140 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw493step0 permutation140 permutation5
    _ = injectiveMoment H node864 := by rfl

def raw494 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]

def raw494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical494 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw494 = injectiveMoment H node1138 := by
  calc
    injectiveMoment H raw494 = injectiveMoment H raw494step0 := by
      have heq : raw494step0 = -raw494 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw494).symm
    injectiveMoment H raw494step0 = injectiveMoment H raw494step1 := by
      have heq : raw494step1 = (fun i j => raw494step0 (permutation117 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw494step0 permutation117 permutation5
    _ = injectiveMoment H node1138 := by rfl

def raw495 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical495 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw495 = injectiveMoment H node336 := by
  rfl

def raw496 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]

def raw496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical496 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw496 = injectiveMoment H node648 := by
  calc
    injectiveMoment H raw496 = injectiveMoment H raw496step0 := by
      have heq : raw496step0 = -raw496 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw496).symm
    injectiveMoment H raw496step0 = injectiveMoment H raw496step1 := by
      have heq : raw496step1 = (fun i j => raw496step0 (permutation99 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw496step0 permutation99 permutation5
    _ = injectiveMoment H node648 := by rfl

def raw497 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]

def raw497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical497 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw497 = injectiveMoment H node662 := by
  calc
    injectiveMoment H raw497 = injectiveMoment H raw497step0 := by
      have heq : raw497step0 = -raw497 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw497).symm
    injectiveMoment H raw497step0 = injectiveMoment H raw497step1 := by
      have heq : raw497step1 = (fun i j => raw497step0 (permutation93 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw497step0 permutation93 permutation5
    _ = injectiveMoment H node662 := by rfl

def raw498 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical498 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw498 = injectiveMoment H node338 := by
  rfl

def raw499 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]

def raw499step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]

def raw499step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

theorem canonical499 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw499 = injectiveMoment H node214 := by
  calc
    injectiveMoment H raw499 = injectiveMoment H raw499step0 := by
      have heq : raw499step0 = -raw499 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw499).symm
    injectiveMoment H raw499step0 = injectiveMoment H raw499step1 := by
      have heq : raw499step1 = (fun i j => raw499step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw499step0 permutation22 permutation5
    _ = injectiveMoment H node214 := by rfl

def raw500 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

theorem canonical500 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw500 = injectiveMoment H node339 := by
  rfl

def raw501 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

theorem canonical501 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw501 = injectiveMoment H node340 := by
  rfl

def raw502 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]

theorem canonical502 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw502 = injectiveMoment H node92 := by
  rfl

def raw503 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def raw503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]

def raw503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem canonical503 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw503 = injectiveMoment H node324 := by
  calc
    injectiveMoment H raw503 = injectiveMoment H raw503step0 := by
      have heq : raw503step0 = -raw503 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw503).symm
    injectiveMoment H raw503step0 = injectiveMoment H raw503step1 := by
      have heq : raw503step1 = (fun i j => raw503step0 (permutation131 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw503step0 permutation131 permutation5
    _ = injectiveMoment H node324 := by rfl

def raw504 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]

def raw504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical504 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw504 = injectiveMoment H node563 := by
  calc
    injectiveMoment H raw504 = injectiveMoment H raw504step0 := by
      have heq : raw504step0 = -raw504 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw504).symm
    injectiveMoment H raw504step0 = injectiveMoment H raw504step1 := by
      have heq : raw504step1 = (fun i j => raw504step0 (permutation146 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw504step0 permutation146 permutation5
    _ = injectiveMoment H node563 := by rfl

def raw505 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def raw505step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-2, -2, 4]]

def raw505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical505 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw505 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw505 = injectiveMoment H raw505step0 := by
      have heq : raw505step0 = -raw505 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw505).symm
    injectiveMoment H raw505step0 = injectiveMoment H raw505step1 := by
      have heq : raw505step1 = (fun i j => raw505step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw505step0 permutation28 permutation5
    _ = injectiveMoment H node155 := by rfl

def raw506 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]

def raw506step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]

def raw506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

theorem canonical506 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw506 = injectiveMoment H node187 := by
  calc
    injectiveMoment H raw506 = injectiveMoment H raw506step0 := by
      have heq : raw506step0 = -raw506 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw506).symm
    injectiveMoment H raw506step0 = injectiveMoment H raw506step1 := by
      have heq : raw506step1 = (fun i j => raw506step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw506step0 permutation22 permutation5
    _ = injectiveMoment H node187 := by rfl

def raw507 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw507step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def raw507step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

theorem canonical507 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw507 = injectiveMoment H node222 := by
  calc
    injectiveMoment H raw507 = injectiveMoment H raw507step0 := by
      have hz : ∀ j, raw507 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw507step0 = (fun i j => raw507 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw507 permutation57 hz
    injectiveMoment H raw507step0 = injectiveMoment H raw507step1 := by
      have heq : raw507step1 = (fun i j => raw507step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw507step0 permutation21 permutation5
    _ = injectiveMoment H node222 := by rfl

def raw508 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]

def raw508step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]

def raw508step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

theorem canonical508 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw508 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw508 = injectiveMoment H raw508step0 := by
      have hz : ∀ j, raw508 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw508step0 = (fun i j => raw508 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw508 permutation15 hz
    injectiveMoment H raw508step0 = injectiveMoment H raw508step1 := by
      have heq : raw508step1 = (fun i j => raw508step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw508step0 permutation7 permutation6
    _ = injectiveMoment H node37 := by rfl

def raw509 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def raw509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 0, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]

def raw509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]

def raw509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

theorem canonical509 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw509 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw509 = injectiveMoment H raw509step0 := by
      have heq : raw509step0 = -raw509 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw509).symm
    injectiveMoment H raw509step0 = injectiveMoment H raw509step1 := by
      have hz : ∀ j, raw509step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw509step1 = (fun i j => raw509step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw509step0 permutation57 hz
    injectiveMoment H raw509step1 = injectiveMoment H raw509step2 := by
      have heq : raw509step2 = (fun i j => raw509step1 (permutation31 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw509step1 permutation31 permutation5
    _ = injectiveMoment H node170 := by rfl

def raw510 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]

def raw510step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 0, 0], ![-1, 2, -1], ![-2, -2, 4]]

def raw510step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-2, -2, 4]]

def raw510step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical510 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw510 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw510 = injectiveMoment H raw510step0 := by
      have heq : raw510step0 = -raw510 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw510).symm
    injectiveMoment H raw510step0 = injectiveMoment H raw510step1 := by
      have hz : ∀ j, raw510step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw510step1 = (fun i j => raw510step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw510step0 permutation15 hz
    injectiveMoment H raw510step1 = injectiveMoment H raw510step2 := by
      have heq : raw510step2 = (fun i j => raw510step1 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw510step1 permutation7 permutation5
    _ = injectiveMoment H node32 := by rfl

def raw511 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def raw511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]

def raw511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]

def raw511step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical511 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw511 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw511 = injectiveMoment H raw511step0 := by
      have heq : raw511step0 = -raw511 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw511).symm
    injectiveMoment H raw511step0 = injectiveMoment H raw511step1 := by
      have hz : ∀ j, raw511step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw511step1 = (fun i j => raw511step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw511step0 permutation57 hz
    injectiveMoment H raw511step1 = injectiveMoment H raw511step2 := by
      have heq : raw511step2 = (fun i j => raw511step1 (permutation27 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw511step1 permutation27 permutation5
    _ = injectiveMoment H node188 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
