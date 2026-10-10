import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4000 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical4000 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4000 = injectiveMoment H node633 := by
  rfl

def raw4001 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical4001 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4001 = injectiveMoment H node634 := by
  rfl

def raw4002 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]

def raw4002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical4002 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4002 = injectiveMoment H node631 := by
  calc
    injectiveMoment H raw4002 = injectiveMoment H raw4002step0 := by
      have heq : raw4002step0 = (fun i j => raw4002 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4002 permutation35 permutation3
    _ = injectiveMoment H node631 := by rfl

def raw4003 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical4003 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4003 = injectiveMoment H node635 := by
  rfl

def raw4004 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1]]

def raw4004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical4004 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4004 = injectiveMoment H node635 := by
  calc
    injectiveMoment H raw4004 = injectiveMoment H raw4004step0 := by
      have heq : raw4004step0 = (fun i j => raw4004 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4004 permutation34 permutation3
    _ = injectiveMoment H node635 := by rfl

def raw4005 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![2, 1, -3]]

def raw4005step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 3, -3], ![0, -2, 2], ![-2, -1, 3]]

def raw4005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

theorem canonical4005 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4005 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw4005 = injectiveMoment H raw4005step0 := by
      have heq : raw4005step0 = -raw4005 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4005).symm
    injectiveMoment H raw4005step0 = injectiveMoment H raw4005step1 := by
      have heq : raw4005step1 = (fun i j => raw4005step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4005step0 permutation32 permutation3
    _ = injectiveMoment H node163 := by rfl

def raw4006 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical4006 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4006 = injectiveMoment H node636 := by
  rfl

def raw4007 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

theorem canonical4007 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4007 = injectiveMoment H node192 := by
  rfl

def raw4008 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

theorem canonical4008 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4008 = injectiveMoment H node637 := by
  rfl

def raw4009 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

theorem canonical4009 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4009 = injectiveMoment H node193 := by
  rfl

def raw4010 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, -1, 0], ![1, 4, -5]]

theorem canonical4010 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4010 = injectiveMoment H node194 := by
  rfl

def raw4011 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 0, -1], ![1, 3, -4]]

theorem canonical4011 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4011 = injectiveMoment H node195 := by
  rfl

def raw4012 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

theorem canonical4012 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4012 = injectiveMoment H node196 := by
  rfl

def raw4013 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 2, -3], ![1, 1, -2]]

def raw4013step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

theorem canonical4013 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4013 = injectiveMoment H node196 := by
  calc
    injectiveMoment H raw4013 = injectiveMoment H raw4013step0 := by
      have heq : raw4013step0 = (fun i j => raw4013 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4013 permutation10 permutation3
    _ = injectiveMoment H node196 := by rfl

def raw4014 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 3, -4], ![1, 0, -1]]

def raw4014step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 0, -1], ![1, 3, -4]]

theorem canonical4014 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4014 = injectiveMoment H node195 := by
  calc
    injectiveMoment H raw4014 = injectiveMoment H raw4014step0 := by
      have heq : raw4014step0 = (fun i j => raw4014 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4014 permutation10 permutation3
    _ = injectiveMoment H node195 := by rfl

def raw4015 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![2, 3, -5]]

def raw4015step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, 3, -3], ![-2, -3, 5]]

def raw4015step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![2, 0, -2]]

theorem canonical4015 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4015 = injectiveMoment H node28 := by
  calc
    injectiveMoment H raw4015 = injectiveMoment H raw4015step0 := by
      have heq : raw4015step0 = -raw4015 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4015).symm
    injectiveMoment H raw4015step0 = injectiveMoment H raw4015step1 := by
      have heq : raw4015step1 = (fun i j => raw4015step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4015step0 permutation8 permutation3
    _ = injectiveMoment H node28 := by rfl

def raw4016 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![-1, 3, -2], ![1, -1, 0], ![2, 0, -2]]

def raw4016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![1, -3, 2], ![-1, 1, 0], ![-2, 0, 2]]

def raw4016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

theorem canonical4016 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4016 = injectiveMoment H node357 := by
  calc
    injectiveMoment H raw4016 = injectiveMoment H raw4016step0 := by
      have heq : raw4016step0 = -raw4016 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4016).symm
    injectiveMoment H raw4016step0 = injectiveMoment H raw4016step1 := by
      have heq : raw4016step1 = (fun i j => raw4016step0 (permutation99 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4016step0 permutation99 permutation5
    _ = injectiveMoment H node357 := by rfl

def raw4017 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![-1, 3, -2], ![1, 0, -1], ![2, -1, -1]]

def raw4017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![1, -3, 2], ![-1, 0, 1], ![-2, 1, 1]]

def raw4017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

theorem canonical4017 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4017 = injectiveMoment H node367 := by
  calc
    injectiveMoment H raw4017 = injectiveMoment H raw4017step0 := by
      have heq : raw4017step0 = -raw4017 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4017).symm
    injectiveMoment H raw4017step0 = injectiveMoment H raw4017step1 := by
      have heq : raw4017step1 = (fun i j => raw4017step0 (permutation93 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4017step0 permutation93 permutation5
    _ = injectiveMoment H node367 := by rfl

def raw4018 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

theorem canonical4018 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4018 = injectiveMoment H node638 := by
  rfl

def raw4019 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

theorem canonical4019 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4019 = injectiveMoment H node639 := by
  rfl

def raw4020 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 0, 0], ![0, 2, -2], ![2, 0, -2]]

def raw4020step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

theorem canonical4020 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4020 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw4020 = injectiveMoment H raw4020step0 := by
      have hz : ∀ j, raw4020 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw4020step0 = (fun i j => raw4020 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4020 permutation80 hz
    _ = injectiveMoment H node197 := by rfl

def raw4021 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 3, -4]]

def raw4021step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical4021 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4021 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw4021 = injectiveMoment H raw4021step0 := by
      have hz : ∀ j, raw4021 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw4021step0 = (fun i j => raw4021 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4021 permutation80 hz
    _ = injectiveMoment H node201 := by rfl

def raw4022 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 2, -3]]

def raw4022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]

def raw4022step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, -2, 3]]

def raw4022step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical4022 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4022 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw4022 = injectiveMoment H raw4022step0 := by
      have heq : raw4022step0 = -raw4022 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4022).symm
    injectiveMoment H raw4022step0 = injectiveMoment H raw4022step1 := by
      have hz : ∀ j, raw4022step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw4022step1 = (fun i j => raw4022step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4022step0 permutation80 hz
    injectiveMoment H raw4022step1 = injectiveMoment H raw4022step2 := by
      have heq : raw4022step2 = (fun i j => raw4022step1 (permutation31 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4022step1 permutation31 permutation5
    _ = injectiveMoment H node169 := by rfl

def raw4023 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical4023 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4023 = injectiveMoment H node641 := by
  rfl

def raw4024 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4024 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4024 = injectiveMoment H node642 := by
  rfl

def raw4025 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical4025 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4025 = injectiveMoment H node644 := by
  rfl

def raw4026 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical4026 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4026 = injectiveMoment H node645 := by
  rfl

def raw4027 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical4027 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4027 = injectiveMoment H node646 := by
  rfl

def raw4028 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1]]

def raw4028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical4028 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4028 = injectiveMoment H node646 := by
  calc
    injectiveMoment H raw4028 = injectiveMoment H raw4028step0 := by
      have heq : raw4028step0 = (fun i j => raw4028 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4028 permutation34 permutation3
    _ = injectiveMoment H node646 := by rfl

def raw4029 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![2, 1, -3]]

def raw4029step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, -1, 1], ![-2, -1, 3]]

def raw4029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical4029 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4029 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw4029 = injectiveMoment H raw4029step0 := by
      have heq : raw4029step0 = -raw4029 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4029).symm
    injectiveMoment H raw4029step0 = injectiveMoment H raw4029step1 := by
      have heq : raw4029step1 = (fun i j => raw4029step0 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4029step0 permutation32 permutation3
    _ = injectiveMoment H node169 := by rfl

def raw4030 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2]]

def raw4030step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

theorem canonical4030 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4030 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw4030 = injectiveMoment H raw4030step0 := by
      have hz : ∀ j, raw4030 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw4030step0 = (fun i j => raw4030 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4030 permutation104 hz
    _ = injectiveMoment H node197 := by rfl

def raw4031 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![0, 1, -1], ![2, -1, -1]]

def raw4031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4031 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4031 = injectiveMoment H node642 := by
  calc
    injectiveMoment H raw4031 = injectiveMoment H raw4031step0 := by
      have heq : raw4031step0 = (fun i j => raw4031 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4031 permutation35 permutation3
    _ = injectiveMoment H node642 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
