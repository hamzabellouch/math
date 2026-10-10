import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5120 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical5120 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5120 = injectiveMoment H node717 := by
  rfl

def raw5121 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]

def raw5121step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical5121 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5121 = injectiveMoment H node118 := by
  calc
    injectiveMoment H raw5121 = injectiveMoment H raw5121step0 := by
      have heq : raw5121step0 = (fun i j => raw5121 (permutation148 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5121 permutation148 permutation2
    _ = injectiveMoment H node118 := by rfl

def raw5122 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]

def raw5122step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical5122 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5122 = injectiveMoment H node231 := by
  calc
    injectiveMoment H raw5122 = injectiveMoment H raw5122step0 := by
      have heq : raw5122step0 = (fun i j => raw5122 (permutation125 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5122 permutation125 permutation2
    _ = injectiveMoment H node231 := by rfl

def raw5123 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]

def raw5123step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]

def raw5123step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5123 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5123 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5123 = injectiveMoment H raw5123step0 := by
      have hz : ∀ j, raw5123 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw5123step0 = (fun i j => raw5123 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5123 permutation241 hz
    injectiveMoment H raw5123step0 = injectiveMoment H raw5123step1 := by
      have hz : ∀ j, raw5123step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5123step1 = (fun i j => raw5123step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5123step0 permutation80 hz
    _ = injectiveMoment H node46 := by rfl

def raw5124 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]

def raw5124step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]

def raw5124step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5124step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5124 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5124 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5124 = injectiveMoment H raw5124step0 := by
      have hz : ∀ j, raw5124 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw5124step0 = (fun i j => raw5124 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5124 permutation241 hz
    injectiveMoment H raw5124step0 = injectiveMoment H raw5124step1 := by
      have hz : ∀ j, raw5124step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5124step1 = (fun i j => raw5124step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5124step0 permutation80 hz
    injectiveMoment H raw5124step1 = injectiveMoment H raw5124step2 := by
      have heq : raw5124step2 = (fun i j => raw5124step1 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5124step1 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5125 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]

def raw5125step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![3, -3]]

def raw5125step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw5125step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical5125 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5125 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5125 = injectiveMoment H raw5125step0 := by
      have hz : ∀ j, raw5125 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5125step0 = (fun i j => raw5125 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5125 permutation104 hz
    injectiveMoment H raw5125step0 = injectiveMoment H raw5125step1 := by
      have hz : ∀ j, raw5125step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5125step1 = (fun i j => raw5125step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5125step0 permutation21 hz
    injectiveMoment H raw5125step1 = injectiveMoment H raw5125step2 := by
      have heq : raw5125step2 = (fun i j => raw5125step1 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5125step1 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw5126 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]

def raw5126step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]

def raw5126step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5126 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5126 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5126 = injectiveMoment H raw5126step0 := by
      have hz : ∀ j, raw5126 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw5126step0 = (fun i j => raw5126 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5126 permutation258 hz
    injectiveMoment H raw5126step0 = injectiveMoment H raw5126step1 := by
      have hz : ∀ j, raw5126step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5126step1 = (fun i j => raw5126step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5126step0 permutation80 hz
    _ = injectiveMoment H node46 := by rfl

def raw5127 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]

def raw5127step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical5127 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5127 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw5127 = injectiveMoment H raw5127step0 := by
      have hz : ∀ j, raw5127 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw5127step0 = (fun i j => raw5127 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5127 permutation221 hz
    _ = injectiveMoment H node232 := by rfl

def raw5128 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]

def raw5128step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5128 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5128 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5128 = injectiveMoment H raw5128step0 := by
      have hz : ∀ j, raw5128 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5128step0 = (fun i j => raw5128 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5128 permutation80 hz
    _ = injectiveMoment H node46 := by rfl

def raw5129 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2], ![0, 0]]

def raw5129step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]

def raw5129step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5129 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5129 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5129 = injectiveMoment H raw5129step0 := by
      have hz : ∀ j, raw5129 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw5129step0 = (fun i j => raw5129 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5129 permutation308 hz
    injectiveMoment H raw5129step0 = injectiveMoment H raw5129step1 := by
      have hz : ∀ j, raw5129step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5129step1 = (fun i j => raw5129step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5129step0 permutation80 hz
    _ = injectiveMoment H node46 := by rfl

def raw5130 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![0, 0], ![1, -1]]

def raw5130step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]

def raw5130step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5130step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5130 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5130 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5130 = injectiveMoment H raw5130step0 := by
      have hz : ∀ j, raw5130 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw5130step0 = (fun i j => raw5130 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5130 permutation258 hz
    injectiveMoment H raw5130step0 = injectiveMoment H raw5130step1 := by
      have hz : ∀ j, raw5130step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5130step1 = (fun i j => raw5130step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5130step0 permutation80 hz
    injectiveMoment H raw5130step1 = injectiveMoment H raw5130step2 := by
      have heq : raw5130step2 = (fun i j => raw5130step1 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5130step1 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5131 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]

def raw5131step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5131step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5131 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5131 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5131 = injectiveMoment H raw5131step0 := by
      have hz : ∀ j, raw5131 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5131step0 = (fun i j => raw5131 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5131 permutation80 hz
    injectiveMoment H raw5131step0 = injectiveMoment H raw5131step1 := by
      have heq : raw5131step1 = (fun i j => raw5131step0 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5131step0 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5132 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![3, -3]]

def raw5132step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw5132step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical5132 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5132 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5132 = injectiveMoment H raw5132step0 := by
      have hz : ∀ j, raw5132 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5132step0 = (fun i j => raw5132 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5132 permutation21 hz
    injectiveMoment H raw5132step0 = injectiveMoment H raw5132step1 := by
      have heq : raw5132step1 = (fun i j => raw5132step0 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5132step0 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw5133 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![3, -3], ![0, 0]]

def raw5133step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![3, -3]]

def raw5133step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw5133step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical5133 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5133 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5133 = injectiveMoment H raw5133step0 := by
      have hz : ∀ j, raw5133 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5133step0 = (fun i j => raw5133 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5133 permutation128 hz
    injectiveMoment H raw5133step0 = injectiveMoment H raw5133step1 := by
      have hz : ∀ j, raw5133step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5133step1 = (fun i j => raw5133step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5133step0 permutation21 hz
    injectiveMoment H raw5133step1 = injectiveMoment H raw5133step2 := by
      have heq : raw5133step2 = (fun i j => raw5133step1 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5133step1 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw5134 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]

def raw5134step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]

def raw5134step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5134 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5134 = injectiveMoment H raw5134step0 := by
      have hz : ∀ j, raw5134 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw5134step0 = (fun i j => raw5134 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5134 permutation258 hz
    injectiveMoment H raw5134step0 = injectiveMoment H raw5134step1 := by
      have hz : ∀ j, raw5134step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5134step1 = (fun i j => raw5134step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5134step0 permutation104 hz
    _ = injectiveMoment H node46 := by rfl

def raw5135 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]

def raw5135step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical5135 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5135 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw5135 = injectiveMoment H raw5135step0 := by
      have hz : ∀ j, raw5135 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw5135step0 = (fun i j => raw5135 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5135 permutation241 hz
    _ = injectiveMoment H node232 := by rfl

def raw5136 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]

def raw5136step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5136 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5136 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5136 = injectiveMoment H raw5136step0 := by
      have hz : ∀ j, raw5136 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5136step0 = (fun i j => raw5136 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5136 permutation104 hz
    _ = injectiveMoment H node46 := by rfl

def raw5137 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]

def raw5137step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]

def raw5137step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5137 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5137 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5137 = injectiveMoment H raw5137step0 := by
      have hz : ∀ j, raw5137 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw5137step0 = (fun i j => raw5137 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5137 permutation308 hz
    injectiveMoment H raw5137step0 = injectiveMoment H raw5137step1 := by
      have hz : ∀ j, raw5137step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5137step1 = (fun i j => raw5137step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5137step0 permutation104 hz
    _ = injectiveMoment H node46 := by rfl

def raw5138 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]

def raw5138step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical5138 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5138 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw5138 = injectiveMoment H raw5138step0 := by
      have hz : ∀ j, raw5138 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw5138step0 = (fun i j => raw5138 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5138 permutation258 hz
    _ = injectiveMoment H node232 := by rfl

def raw5139 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical5139 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5139 = injectiveMoment H node232 := by
  rfl

def raw5140 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]

def raw5140step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical5140 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5140 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw5140 = injectiveMoment H raw5140step0 := by
      have hz : ∀ j, raw5140 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw5140step0 = (fun i j => raw5140 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5140 permutation308 hz
    _ = injectiveMoment H node232 := by rfl

def raw5141 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5141 = injectiveMoment H node46 := by
  rfl

def raw5142 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![0, 0]]

def raw5142step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5142 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5142 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5142 = injectiveMoment H raw5142step0 := by
      have hz : ∀ j, raw5142 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5142step0 = (fun i j => raw5142 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5142 permutation128 hz
    _ = injectiveMoment H node46 := by rfl

def raw5143 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![0, 0], ![0, 0]]

def raw5143step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![0, 0]]

def raw5143step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5143 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5143 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5143 = injectiveMoment H raw5143step0 := by
      have hz : ∀ j, raw5143 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw5143step0 = (fun i j => raw5143 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5143 permutation308 hz
    injectiveMoment H raw5143step0 = injectiveMoment H raw5143step1 := by
      have hz : ∀ j, raw5143step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5143step1 = (fun i j => raw5143step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5143step0 permutation128 hz
    _ = injectiveMoment H node46 := by rfl

def raw5144 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![-1, 1], ![1, -1], ![1, -1]]

def raw5144step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical5144 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5144 = injectiveMoment H node717 := by
  calc
    injectiveMoment H raw5144 = injectiveMoment H raw5144step0 := by
      have heq : raw5144step0 = (fun i j => raw5144 (permutation159 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5144 permutation159 permutation1
    _ = injectiveMoment H node717 := by rfl

def raw5145 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![-1, 1], ![2, -2]]

def raw5145step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical5145 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5145 = injectiveMoment H node231 := by
  calc
    injectiveMoment H raw5145 = injectiveMoment H raw5145step0 := by
      have heq : raw5145step0 = (fun i j => raw5145 (permutation101 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5145 permutation101 permutation2
    _ = injectiveMoment H node231 := by rfl

def raw5146 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![0, 0], ![0, 0], ![1, -1]]

def raw5146step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![0, 0], ![1, -1]]

def raw5146step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5146step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5146 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5146 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5146 = injectiveMoment H raw5146step0 := by
      have hz : ∀ j, raw5146 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw5146step0 = (fun i j => raw5146 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5146 permutation258 hz
    injectiveMoment H raw5146step0 = injectiveMoment H raw5146step1 := by
      have hz : ∀ j, raw5146step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5146step1 = (fun i j => raw5146step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5146step0 permutation104 hz
    injectiveMoment H raw5146step1 = injectiveMoment H raw5146step2 := by
      have heq : raw5146step2 = (fun i j => raw5146step1 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5146step1 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5147 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![0, 0], ![1, -1]]

def raw5147step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5147step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5147 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5147 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5147 = injectiveMoment H raw5147step0 := by
      have hz : ∀ j, raw5147 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5147step0 = (fun i j => raw5147 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5147 permutation104 hz
    injectiveMoment H raw5147step0 = injectiveMoment H raw5147step1 := by
      have heq : raw5147step1 = (fun i j => raw5147step0 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5147step0 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5148 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![0, 0], ![1, -1], ![0, 0]]

def raw5148step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![0, 0], ![1, -1]]

def raw5148step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5148step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5148 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5148 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5148 = injectiveMoment H raw5148step0 := by
      have hz : ∀ j, raw5148 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw5148step0 = (fun i j => raw5148 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5148 permutation308 hz
    injectiveMoment H raw5148step0 = injectiveMoment H raw5148step1 := by
      have hz : ∀ j, raw5148step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5148step1 = (fun i j => raw5148step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5148step0 permutation104 hz
    injectiveMoment H raw5148step1 = injectiveMoment H raw5148step2 := by
      have heq : raw5148step2 = (fun i j => raw5148step1 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5148step1 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5149 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5149step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5149 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5149 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5149 = injectiveMoment H raw5149step0 := by
      have heq : raw5149step0 = (fun i j => raw5149 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5149 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5150 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1], ![0, 0]]

def raw5150step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5150step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5150 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5150 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5150 = injectiveMoment H raw5150step0 := by
      have hz : ∀ j, raw5150 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5150step0 = (fun i j => raw5150 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5150 permutation128 hz
    injectiveMoment H raw5150step0 = injectiveMoment H raw5150step1 := by
      have heq : raw5150step1 = (fun i j => raw5150step0 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5150step0 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5151 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw5151step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical5151 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5151 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5151 = injectiveMoment H raw5151step0 := by
      have heq : raw5151step0 = (fun i j => raw5151 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5151 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
