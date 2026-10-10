import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9504 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1]]

def raw9504step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical9504 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9504 = injectiveMoment H node3442 := by
  calc
    injectiveMoment H raw9504 = injectiveMoment H raw9504step0 := by
      have heq : raw9504step0 = (fun i j => raw9504 (permutation249 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9504 permutation249 permutation18
    _ = injectiveMoment H node3442 := by rfl

def raw9505 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![-2, 1, 0, 1], ![1, -2, 2, -1]]

def raw9505step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

theorem canonical9505 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9505 = injectiveMoment H node3261 := by
  calc
    injectiveMoment H raw9505 = injectiveMoment H raw9505step0 := by
      have heq : raw9505step0 = (fun i j => raw9505 (permutation334 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9505 permutation334 permutation16
    _ = injectiveMoment H node3261 := by rfl

def raw9506 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 1, -1, 2], ![1, -2, 2, -1]]

def raw9506step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

theorem canonical9506 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9506 = injectiveMoment H node3260 := by
  calc
    injectiveMoment H raw9506 = injectiveMoment H raw9506step0 := by
      have heq : raw9506step0 = (fun i j => raw9506 (permutation259 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9506 permutation259 permutation9
    _ = injectiveMoment H node3260 := by rfl

def raw9507 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, -2, 1, 0]]

def raw9507step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical9507 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9507 = injectiveMoment H node3205 := by
  calc
    injectiveMoment H raw9507 = injectiveMoment H raw9507step0 := by
      have heq : raw9507step0 = (fun i j => raw9507 (permutation264 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9507 permutation264 permutation11
    _ = injectiveMoment H node3205 := by rfl

def raw9508 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, -2, 3], ![1, -2, 2, -1]]

def raw9508step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

theorem canonical9508 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9508 = injectiveMoment H node3235 := by
  calc
    injectiveMoment H raw9508 = injectiveMoment H raw9508step0 := by
      have heq : raw9508step0 = (fun i j => raw9508 (permutation259 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9508 permutation259 permutation9
    _ = injectiveMoment H node3235 := by rfl

def raw9509 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![1, -2, 1, 0]]

def raw9509step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical9509 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9509 = injectiveMoment H node3032 := by
  calc
    injectiveMoment H raw9509 = injectiveMoment H raw9509step0 := by
      have heq : raw9509step0 = (fun i j => raw9509 (permutation264 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9509 permutation264 permutation11
    _ = injectiveMoment H node3032 := by rfl

def raw9510 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -2, 0, 1]]

def raw9510step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical9510 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9510 = injectiveMoment H node3432 := by
  calc
    injectiveMoment H raw9510 = injectiveMoment H raw9510step0 := by
      have heq : raw9510step0 = (fun i j => raw9510 (permutation191 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9510 permutation191 permutation21
    _ = injectiveMoment H node3432 := by rfl

def raw9511 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![0, -1, -2, 3]]

def raw9511step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![-1, -2, 3]]

def raw9511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

theorem canonical9511 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9511 = injectiveMoment H node267 := by
  calc
    injectiveMoment H raw9511 = injectiveMoment H raw9511step0 := by
      have hz : ∀ i, raw9511 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9511step0 = (fun i j => raw9511 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9511 permutation9 hz
    injectiveMoment H raw9511step0 = injectiveMoment H raw9511step1 := by
      have heq : raw9511step1 = (fun i j => raw9511step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9511step0 permutation27 permutation3
    _ = injectiveMoment H node267 := by rfl

def raw9512 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -2, 0, 2]]

def raw9512step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![-2, 0, 2]]

def raw9512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical9512 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9512 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw9512 = injectiveMoment H raw9512step0 := by
      have hz : ∀ i, raw9512 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9512step0 = (fun i j => raw9512 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9512 permutation9 hz
    injectiveMoment H raw9512step0 = injectiveMoment H raw9512step1 := by
      have heq : raw9512step1 = (fun i j => raw9512step0 (permutation14 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9512step0 permutation14 permutation5
    _ = injectiveMoment H node291 := by rfl

def raw9513 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 0, 1], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def raw9513step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw9513step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9513 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9513 = injectiveMoment H node2948 := by
  calc
    injectiveMoment H raw9513 = injectiveMoment H raw9513step0 := by
      have heq : raw9513step0 = -raw9513 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9513).symm
    injectiveMoment H raw9513step0 = injectiveMoment H raw9513step1 := by
      have heq : raw9513step1 = (fun i j => raw9513step0 (permutation353 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9513step0 permutation353 permutation17
    _ = injectiveMoment H node2948 := by rfl

def raw9514 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def raw9514step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw9514step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical9514 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9514 = injectiveMoment H node2951 := by
  calc
    injectiveMoment H raw9514 = injectiveMoment H raw9514step0 := by
      have heq : raw9514step0 = -raw9514 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9514).symm
    injectiveMoment H raw9514step0 = injectiveMoment H raw9514step1 := by
      have heq : raw9514step1 = (fun i j => raw9514step0 (permutation350 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9514step0 permutation350 permutation17
    _ = injectiveMoment H node2951 := by rfl

def raw9515 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 2, 2, -3]]

def raw9515step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![1, -2, -2, 3]]

def raw9515step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical9515 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9515 = injectiveMoment H node3236 := by
  calc
    injectiveMoment H raw9515 = injectiveMoment H raw9515step0 := by
      have heq : raw9515step0 = -raw9515 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9515).symm
    injectiveMoment H raw9515step0 = injectiveMoment H raw9515step1 := by
      have heq : raw9515step1 = (fun i j => raw9515step0 (permutation336 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9515step0 permutation336 permutation15
    _ = injectiveMoment H node3236 := by rfl

def raw9516 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 2, 1, -3]]

def raw9516step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical9516 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9516 = injectiveMoment H node3070 := by
  calc
    injectiveMoment H raw9516 = injectiveMoment H raw9516step0 := by
      have heq : raw9516step0 = (fun i j => raw9516 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9516 permutation262 permutation9
    _ = injectiveMoment H node3070 := by rfl

def raw9517 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 2, 2, -3]]

def raw9517step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![1, -2, -2, 3]]

def raw9517step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

theorem canonical9517 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9517 = injectiveMoment H node3227 := by
  calc
    injectiveMoment H raw9517 = injectiveMoment H raw9517step0 := by
      have heq : raw9517step0 = -raw9517 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9517).symm
    injectiveMoment H raw9517step0 = injectiveMoment H raw9517step1 := by
      have heq : raw9517step1 = (fun i j => raw9517step0 (permutation377 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9517step0 permutation377 permutation15
    _ = injectiveMoment H node3227 := by rfl

def raw9518 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![-1, 2, 1, -2]]

def raw9518step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 0, 1, 0], ![1, 1, -1, -1], ![1, -2, -1, 2]]

def raw9518step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical9518 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9518 = injectiveMoment H node3247 := by
  calc
    injectiveMoment H raw9518 = injectiveMoment H raw9518step0 := by
      have heq : raw9518step0 = -raw9518 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9518).symm
    injectiveMoment H raw9518step0 = injectiveMoment H raw9518step1 := by
      have heq : raw9518step1 = (fun i j => raw9518step0 (permutation377 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9518step0 permutation377 permutation15
    _ = injectiveMoment H node3247 := by rfl

def raw9519 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 2, 1]]

def raw9519step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical9519 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9519 = injectiveMoment H node3066 := by
  calc
    injectiveMoment H raw9519 = injectiveMoment H raw9519step0 := by
      have heq : raw9519step0 = (fun i j => raw9519 (permutation335 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9519 permutation335 permutation10
    _ = injectiveMoment H node3066 := by rfl

def raw9520 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 2, 1, -2]]

def raw9520step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -2, -1, 2]]

def raw9520step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem canonical9520 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9520 = injectiveMoment H node3025 := by
  calc
    injectiveMoment H raw9520 = injectiveMoment H raw9520step0 := by
      have heq : raw9520step0 = -raw9520 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9520).symm
    injectiveMoment H raw9520step0 = injectiveMoment H raw9520step1 := by
      have heq : raw9520step1 = (fun i j => raw9520step0 (permutation344 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9520step0 permutation344 permutation17
    _ = injectiveMoment H node3025 := by rfl

def raw9521 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 2, 2, -2]]

def raw9521step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw9521step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem canonical9521 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9521 = injectiveMoment H node3308 := by
  calc
    injectiveMoment H raw9521 = injectiveMoment H raw9521step0 := by
      have heq : raw9521step0 = -raw9521 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9521).symm
    injectiveMoment H raw9521step0 = injectiveMoment H raw9521step1 := by
      have heq : raw9521step1 = (fun i j => raw9521step0 (permutation377 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9521step0 permutation377 permutation15
    _ = injectiveMoment H node3308 := by rfl

def raw9522 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def raw9522step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical9522 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9522 = injectiveMoment H node3068 := by
  calc
    injectiveMoment H raw9522 = injectiveMoment H raw9522step0 := by
      have heq : raw9522step0 = (fun i j => raw9522 (permutation312 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9522 permutation312 permutation9
    _ = injectiveMoment H node3068 := by rfl

def raw9523 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def raw9523step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 1, 1, -1], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw9523step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical9523 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9523 = injectiveMoment H node2951 := by
  calc
    injectiveMoment H raw9523 = injectiveMoment H raw9523step0 := by
      have heq : raw9523step0 = -raw9523 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9523).symm
    injectiveMoment H raw9523step0 = injectiveMoment H raw9523step1 := by
      have heq : raw9523step1 = (fun i j => raw9523step0 (permutation349 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9523step0 permutation349 permutation17
    _ = injectiveMoment H node2951 := by rfl

def raw9524 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, -1, 1], ![-1, 0, -1, 2], ![-1, 2, 2, -3]]

def raw9524step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 1, 1, -1], ![1, 0, 1, -2], ![1, -2, -2, 3]]

def raw9524step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical9524 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9524 = injectiveMoment H node3236 := by
  calc
    injectiveMoment H raw9524 = injectiveMoment H raw9524step0 := by
      have heq : raw9524step0 = -raw9524 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9524).symm
    injectiveMoment H raw9524step0 = injectiveMoment H raw9524step1 := by
      have heq : raw9524step1 = (fun i j => raw9524step0 (permutation335 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9524step0 permutation335 permutation15
    _ = injectiveMoment H node3236 := by rfl

def raw9525 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 2, 1, -3]]

def raw9525step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical9525 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9525 = injectiveMoment H node2957 := by
  calc
    injectiveMoment H raw9525 = injectiveMoment H raw9525step0 := by
      have heq : raw9525step0 = (fun i j => raw9525 (permutation262 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9525 permutation262 permutation11
    _ = injectiveMoment H node2957 := by rfl

def raw9526 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 2, 0, -2]]

def raw9526step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical9526 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9526 = injectiveMoment H node3426 := by
  calc
    injectiveMoment H raw9526 = injectiveMoment H raw9526step0 := by
      have heq : raw9526step0 = (fun i j => raw9526 (permutation196 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9526 permutation196 permutation21
    _ = injectiveMoment H node3426 := by rfl

def raw9527 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -2, 3], ![-1, 2, 2, -3]]

def raw9527step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, 2, -3], ![1, -2, -2, 3]]

def raw9527step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9527 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9527 = injectiveMoment H node3237 := by
  calc
    injectiveMoment H raw9527 = injectiveMoment H raw9527step0 := by
      have heq : raw9527step0 = -raw9527 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9527).symm
    injectiveMoment H raw9527step0 = injectiveMoment H raw9527step1 := by
      have heq : raw9527step1 = (fun i j => raw9527step0 (permutation335 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9527step0 permutation335 permutation15
    _ = injectiveMoment H node3237 := by rfl

def raw9528 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 2, 1, -2]]

def raw9528step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![1, -2, -1, 2]]

def raw9528step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical9528 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9528 = injectiveMoment H node3037 := by
  calc
    injectiveMoment H raw9528 = injectiveMoment H raw9528step0 := by
      have heq : raw9528step0 = -raw9528 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9528).symm
    injectiveMoment H raw9528step0 = injectiveMoment H raw9528step1 := by
      have heq : raw9528step1 = (fun i j => raw9528step0 (permutation335 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9528step0 permutation335 permutation17
    _ = injectiveMoment H node3037 := by rfl

def raw9529 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-2, -1, 1, 2], ![0, 2, 1, -3]]

def raw9529step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem canonical9529 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9529 = injectiveMoment H node3071 := by
  calc
    injectiveMoment H raw9529 = injectiveMoment H raw9529step0 := by
      have heq : raw9529step0 = (fun i j => raw9529 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9529 permutation262 permutation9
    _ = injectiveMoment H node3071 := by rfl

def raw9530 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-1, -1, 0, 2], ![-1, 2, 2, -3]]

def raw9530step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 2, -1], ![1, 1, 0, -2], ![1, -2, -2, 3]]

def raw9530step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical9530 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9530 = injectiveMoment H node3231 := by
  calc
    injectiveMoment H raw9530 = injectiveMoment H raw9530step0 := by
      have heq : raw9530step0 = -raw9530 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9530).symm
    injectiveMoment H raw9530step0 = injectiveMoment H raw9530step1 := by
      have heq : raw9530step1 = (fun i j => raw9530step0 (permutation377 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9530step0 permutation377 permutation15
    _ = injectiveMoment H node3231 := by rfl

def raw9531 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-1, -1, 1, 1], ![-1, 2, 1, -2]]

def raw9531step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 2, -1], ![1, 1, -1, -1], ![1, -2, -1, 2]]

def raw9531step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical9531 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9531 = injectiveMoment H node3250 := by
  calc
    injectiveMoment H raw9531 = injectiveMoment H raw9531step0 := by
      have heq : raw9531step0 = -raw9531 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9531).symm
    injectiveMoment H raw9531step0 = injectiveMoment H raw9531step1 := by
      have heq : raw9531step1 = (fun i j => raw9531step0 (permutation377 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9531step0 permutation377 permutation15
    _ = injectiveMoment H node3250 := by rfl

def raw9532 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![0, 2, 0, -2], ![-2, -1, 2, 1]]

def raw9532step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical9532 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9532 = injectiveMoment H node3065 := by
  calc
    injectiveMoment H raw9532 = injectiveMoment H raw9532step0 := by
      have heq : raw9532step0 = (fun i j => raw9532 (permutation335 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9532 permutation335 permutation10
    _ = injectiveMoment H node3065 := by rfl

def raw9533 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 2, 1, -3]]

def raw9533step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 1, 0, -3], ![0, -2, -1, 3]]

def raw9533step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

theorem canonical9533 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9533 = injectiveMoment H node2954 := by
  calc
    injectiveMoment H raw9533 = injectiveMoment H raw9533step0 := by
      have heq : raw9533step0 = -raw9533 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9533).symm
    injectiveMoment H raw9533step0 = injectiveMoment H raw9533step1 := by
      have heq : raw9533step1 = (fun i j => raw9533step0 (permutation343 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9533step0 permutation343 permutation17
    _ = injectiveMoment H node2954 := by rfl

def raw9534 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 2, 0, -2]]

def raw9534step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9534 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9534 = injectiveMoment H node3069 := by
  calc
    injectiveMoment H raw9534 = injectiveMoment H raw9534step0 := by
      have heq : raw9534step0 = (fun i j => raw9534 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9534 permutation262 permutation9
    _ = injectiveMoment H node3069 := by rfl

def raw9535 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 1, -2]]

def raw9535step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -1, -1, 2]]

def raw9535step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical9535 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9535 = injectiveMoment H node3391 := by
  calc
    injectiveMoment H raw9535 = injectiveMoment H raw9535step0 := by
      have heq : raw9535step0 = -raw9535 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9535).symm
    injectiveMoment H raw9535step0 = injectiveMoment H raw9535step1 := by
      have heq : raw9535step1 = (fun i j => raw9535step0 (permutation353 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9535step0 permutation353 permutation17
    _ = injectiveMoment H node3391 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
