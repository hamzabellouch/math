import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5152 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3], ![0, 0]]

def raw5152step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw5152step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical5152 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5152 = injectiveMoment H node10 := by
  clear _hH
  calc
    injectiveMoment H raw5152 = injectiveMoment H raw5152step0 := by
      have hz : ∀ j, raw5152 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5152step0 = (fun i j => raw5152 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5152 permutation27 hz
    injectiveMoment H raw5152step0 = injectiveMoment H raw5152step1 := by
      have heq : raw5152step1 = (fun i j => raw5152step0 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5152step0 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw5153 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]

def raw5153step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]

def raw5153step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5153 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5153 = injectiveMoment H node46 := by
  clear _hH
  calc
    injectiveMoment H raw5153 = injectiveMoment H raw5153step0 := by
      have hz : ∀ j, raw5153 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw5153step0 = (fun i j => raw5153 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5153 permutation241 hz
    injectiveMoment H raw5153step0 = injectiveMoment H raw5153step1 := by
      have hz : ∀ j, raw5153step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw5153step1 = (fun i j => raw5153step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5153step0 permutation57 hz
    _ = injectiveMoment H node46 := by rfl

def raw5154 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![0, 0], ![3, -3]]

def raw5154step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![3, -3]]

def raw5154step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw5154step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical5154 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5154 = injectiveMoment H node10 := by
  clear _hH
  calc
    injectiveMoment H raw5154 = injectiveMoment H raw5154step0 := by
      have hz : ∀ j, raw5154 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5154step0 = (fun i j => raw5154 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5154 permutation104 hz
    injectiveMoment H raw5154step0 = injectiveMoment H raw5154step1 := by
      have hz : ∀ j, raw5154step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5154step1 = (fun i j => raw5154step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5154step0 permutation15 hz
    injectiveMoment H raw5154step1 = injectiveMoment H raw5154step2 := by
      have heq : raw5154step2 = (fun i j => raw5154step1 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5154step1 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw5155 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]

def raw5155step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]

def raw5155step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5155 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5155 = injectiveMoment H node46 := by
  clear _hH
  calc
    injectiveMoment H raw5155 = injectiveMoment H raw5155step0 := by
      have hz : ∀ j, raw5155 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw5155step0 = (fun i j => raw5155 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5155 permutation258 hz
    injectiveMoment H raw5155step0 = injectiveMoment H raw5155step1 := by
      have hz : ∀ j, raw5155step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw5155step1 = (fun i j => raw5155step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5155step0 permutation57 hz
    _ = injectiveMoment H node46 := by rfl

def raw5156 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw5156step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical5156 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5156 = injectiveMoment H node232 := by
  clear _hH
  calc
    injectiveMoment H raw5156 = injectiveMoment H raw5156step0 := by
      have hz : ∀ j, raw5156 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw5156step0 = (fun i j => raw5156 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5156 permutation202 hz
    _ = injectiveMoment H node232 := by rfl

def raw5157 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]

def raw5157step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5157 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5157 = injectiveMoment H node46 := by
  clear _hH
  calc
    injectiveMoment H raw5157 = injectiveMoment H raw5157step0 := by
      have hz : ∀ j, raw5157 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw5157step0 = (fun i j => raw5157 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5157 permutation57 hz
    _ = injectiveMoment H node46 := by rfl

def raw5158 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2], ![0, 0]]

def raw5158step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]

def raw5158step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5158 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5158 = injectiveMoment H node46 := by
  clear _hH
  calc
    injectiveMoment H raw5158 = injectiveMoment H raw5158step0 := by
      have hz : ∀ j, raw5158 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw5158step0 = (fun i j => raw5158 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5158 permutation308 hz
    injectiveMoment H raw5158step0 = injectiveMoment H raw5158step1 := by
      have hz : ∀ j, raw5158step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw5158step1 = (fun i j => raw5158step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5158step0 permutation57 hz
    _ = injectiveMoment H node46 := by rfl

def raw5159 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]

def raw5159step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5159step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5159 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5159 = injectiveMoment H node46 := by
  clear _hH
  calc
    injectiveMoment H raw5159 = injectiveMoment H raw5159step0 := by
      have hz : ∀ j, raw5159 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw5159step0 = (fun i j => raw5159 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5159 permutation57 hz
    injectiveMoment H raw5159step0 = injectiveMoment H raw5159step1 := by
      have heq : raw5159step1 = (fun i j => raw5159step0 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5159step0 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5160 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![1, -1], ![0, 0]]

def raw5160step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]

def raw5160step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5160step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5160 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5160 = injectiveMoment H node46 := by
  clear _hH
  calc
    injectiveMoment H raw5160 = injectiveMoment H raw5160step0 := by
      have hz : ∀ j, raw5160 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw5160step0 = (fun i j => raw5160 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5160 permutation308 hz
    injectiveMoment H raw5160step0 = injectiveMoment H raw5160step1 := by
      have hz : ∀ j, raw5160step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw5160step1 = (fun i j => raw5160step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5160step0 permutation57 hz
    injectiveMoment H raw5160step1 = injectiveMoment H raw5160step2 := by
      have heq : raw5160step2 = (fun i j => raw5160step1 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5160step1 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5161 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![3, -3]]

def raw5161step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw5161step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical5161 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5161 = injectiveMoment H node10 := by
  clear _hH
  calc
    injectiveMoment H raw5161 = injectiveMoment H raw5161step0 := by
      have hz : ∀ j, raw5161 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5161step0 = (fun i j => raw5161 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5161 permutation15 hz
    injectiveMoment H raw5161step0 = injectiveMoment H raw5161step1 := by
      have heq : raw5161step1 = (fun i j => raw5161step0 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5161step0 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw5162 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]

def raw5162step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]

def raw5162step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw5162step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5162 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5162 = injectiveMoment H node46 := by
  clear _hH
  calc
    injectiveMoment H raw5162 = injectiveMoment H raw5162step0 := by
      have hz : ∀ j, raw5162 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw5162step0 = (fun i j => raw5162 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5162 permutation221 hz
    injectiveMoment H raw5162step0 = injectiveMoment H raw5162step1 := by
      have hz : ∀ j, raw5162step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw5162step1 = (fun i j => raw5162step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5162step0 permutation57 hz
    injectiveMoment H raw5162step1 = injectiveMoment H raw5162step2 := by
      have heq : raw5162step2 = (fun i j => raw5162step1 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5162step1 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5163 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![2, -2]]

def raw5163step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![2, -2]]

def raw5163step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def raw5163step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2]]

def raw5163step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical5163 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5163 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5163 = injectiveMoment H raw5163step0 := by
      have hz : ∀ j, raw5163 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw5163step0 = (fun i j => raw5163 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5163 permutation258 hz
    injectiveMoment H raw5163step0 = injectiveMoment H raw5163step1 := by
      have hz : ∀ j, raw5163step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5163step1 = (fun i j => raw5163step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5163step0 permutation104 hz
    injectiveMoment H raw5163step1 = injectiveMoment H raw5163step2 := by
      have hz : ∀ j, raw5163step1 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5163step2 = (fun i j => raw5163step1 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5163step1 permutation21 hz
    injectiveMoment H raw5163step2 = injectiveMoment H raw5163step3 := by
      have hz : ∀ j, raw5163step2 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5163step3 = (fun i j => raw5163step2 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5163step2 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

def raw5164 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]

def raw5164step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]

def raw5164step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5164step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical5164 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5164 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5164 = injectiveMoment H raw5164step0 := by
      have hz : ∀ j, raw5164 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw5164step0 = (fun i j => raw5164 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5164 permutation241 hz
    injectiveMoment H raw5164step0 = injectiveMoment H raw5164step1 := by
      have hz : ∀ j, raw5164step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5164step1 = (fun i j => raw5164step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5164step0 permutation80 hz
    injectiveMoment H raw5164step1 = injectiveMoment H raw5164step2 := by
      have hz : ∀ j, raw5164step1 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5164step2 = (fun i j => raw5164step1 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5164step1 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

def raw5165 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![2, -2]]

def raw5165step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def raw5165step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2]]

def raw5165step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical5165 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5165 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5165 = injectiveMoment H raw5165step0 := by
      have hz : ∀ j, raw5165 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5165step0 = (fun i j => raw5165 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5165 permutation104 hz
    injectiveMoment H raw5165step0 = injectiveMoment H raw5165step1 := by
      have hz : ∀ j, raw5165step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5165step1 = (fun i j => raw5165step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5165step0 permutation21 hz
    injectiveMoment H raw5165step1 = injectiveMoment H raw5165step2 := by
      have hz : ∀ j, raw5165step1 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5165step2 = (fun i j => raw5165step1 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5165step1 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

def raw5166 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![1, -1], ![0, 0], ![1, -1]]

def raw5166step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]

def raw5166step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5166step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical5166 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5166 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5166 = injectiveMoment H raw5166step0 := by
      have hz : ∀ j, raw5166 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw5166step0 = (fun i j => raw5166 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5166 permutation258 hz
    injectiveMoment H raw5166step0 = injectiveMoment H raw5166step1 := by
      have hz : ∀ j, raw5166step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5166step1 = (fun i j => raw5166step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5166step0 permutation80 hz
    injectiveMoment H raw5166step1 = injectiveMoment H raw5166step2 := by
      have hz : ∀ j, raw5166step1 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5166step2 = (fun i j => raw5166step1 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5166step1 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

def raw5167 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]

def raw5167step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5167step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical5167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5167 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5167 = injectiveMoment H raw5167step0 := by
      have hz : ∀ j, raw5167 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5167step0 = (fun i j => raw5167 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5167 permutation80 hz
    injectiveMoment H raw5167step0 = injectiveMoment H raw5167step1 := by
      have hz : ∀ j, raw5167step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5167step1 = (fun i j => raw5167step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5167step0 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

def raw5168 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![1, -1], ![1, -1], ![0, 0]]

def raw5168step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]

def raw5168step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5168step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical5168 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5168 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5168 = injectiveMoment H raw5168step0 := by
      have hz : ∀ j, raw5168 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw5168step0 = (fun i j => raw5168 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5168 permutation308 hz
    injectiveMoment H raw5168step0 = injectiveMoment H raw5168step1 := by
      have hz : ∀ j, raw5168step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5168step1 = (fun i j => raw5168step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5168step0 permutation80 hz
    injectiveMoment H raw5168step1 = injectiveMoment H raw5168step2 := by
      have hz : ∀ j, raw5168step1 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5168step2 = (fun i j => raw5168step1 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5168step1 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

def raw5169 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def raw5169step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2]]

def raw5169step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical5169 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5169 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5169 = injectiveMoment H raw5169step0 := by
      have hz : ∀ j, raw5169 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5169step0 = (fun i j => raw5169 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169 permutation21 hz
    injectiveMoment H raw5169step0 = injectiveMoment H raw5169step1 := by
      have hz : ∀ j, raw5169step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5169step1 = (fun i j => raw5169step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169step0 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

def raw5170 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![0, 0]]

def raw5170step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def raw5170step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2]]

def raw5170step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical5170 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5170 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5170 = injectiveMoment H raw5170step0 := by
      have hz : ∀ j, raw5170 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5170step0 = (fun i j => raw5170 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5170 permutation128 hz
    injectiveMoment H raw5170step0 = injectiveMoment H raw5170step1 := by
      have hz : ∀ j, raw5170step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5170step1 = (fun i j => raw5170step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5170step0 permutation21 hz
    injectiveMoment H raw5170step1 = injectiveMoment H raw5170step2 := by
      have hz : ∀ j, raw5170step1 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5170step2 = (fun i j => raw5170step1 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5170step1 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

def raw5171 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![0, 0], ![2, -2]]

def raw5171step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![2, -2]]

def raw5171step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw5171step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5171 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5171 = injectiveMoment H node46 := by
  clear _hH
  calc
    injectiveMoment H raw5171 = injectiveMoment H raw5171step0 := by
      have hz : ∀ j, raw5171 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw5171step0 = (fun i j => raw5171 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5171 permutation258 hz
    injectiveMoment H raw5171step0 = injectiveMoment H raw5171step1 := by
      have hz : ∀ j, raw5171step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw5171step1 = (fun i j => raw5171step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5171step0 permutation57 hz
    injectiveMoment H raw5171step1 = injectiveMoment H raw5171step2 := by
      have heq : raw5171step2 = (fun i j => raw5171step1 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5171step1 permutation11 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5172 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]

def raw5172step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]

def raw5172step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical5172 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5172 = injectiveMoment H node232 := by
  clear _hH
  calc
    injectiveMoment H raw5172 = injectiveMoment H raw5172step0 := by
      have hz : ∀ j, raw5172 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw5172step0 = (fun i j => raw5172 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5172 permutation202 hz
    injectiveMoment H raw5172step0 = injectiveMoment H raw5172step1 := by
      have heq : raw5172step1 = (fun i j => raw5172step0 (permutation39 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5172step0 permutation39 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw5173 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![2, -2]]

def raw5173step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw5173step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5173 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5173 = injectiveMoment H node46 := by
  clear _hH
  calc
    injectiveMoment H raw5173 = injectiveMoment H raw5173step0 := by
      have hz : ∀ j, raw5173 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw5173step0 = (fun i j => raw5173 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5173 permutation57 hz
    injectiveMoment H raw5173step0 = injectiveMoment H raw5173step1 := by
      have heq : raw5173step1 = (fun i j => raw5173step0 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5173step0 permutation11 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5174 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![0, 0], ![0, 0], ![1, -1]]

def raw5174step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![0, 0], ![1, -1]]

def raw5174step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5174step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical5174 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5174 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5174 = injectiveMoment H raw5174step0 := by
      have hz : ∀ j, raw5174 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw5174step0 = (fun i j => raw5174 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5174 permutation258 hz
    injectiveMoment H raw5174step0 = injectiveMoment H raw5174step1 := by
      have hz : ∀ j, raw5174step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5174step1 = (fun i j => raw5174step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5174step0 permutation104 hz
    injectiveMoment H raw5174step1 = injectiveMoment H raw5174step2 := by
      have hz : ∀ j, raw5174step1 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5174step2 = (fun i j => raw5174step1 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5174step1 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

def raw5175 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![0, 0], ![1, -1]]

def raw5175step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5175step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical5175 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5175 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5175 = injectiveMoment H raw5175step0 := by
      have hz : ∀ j, raw5175 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5175step0 = (fun i j => raw5175 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5175 permutation104 hz
    injectiveMoment H raw5175step0 = injectiveMoment H raw5175step1 := by
      have hz : ∀ j, raw5175step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5175step1 = (fun i j => raw5175step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5175step0 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

def raw5176 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![0, 0], ![1, -1], ![0, 0]]

def raw5176step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![0, 0], ![1, -1]]

def raw5176step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5176step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical5176 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5176 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5176 = injectiveMoment H raw5176step0 := by
      have hz : ∀ j, raw5176 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw5176step0 = (fun i j => raw5176 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5176 permutation308 hz
    injectiveMoment H raw5176step0 = injectiveMoment H raw5176step1 := by
      have hz : ∀ j, raw5176step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5176step1 = (fun i j => raw5176step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5176step0 permutation104 hz
    injectiveMoment H raw5176step1 = injectiveMoment H raw5176step2 := by
      have hz : ∀ j, raw5176step1 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5176step2 = (fun i j => raw5176step1 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5176step1 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

def raw5177 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5177step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical5177 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5177 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5177 = injectiveMoment H raw5177step0 := by
      have hz : ∀ j, raw5177 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5177step0 = (fun i j => raw5177 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5177 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

def raw5178 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]

def raw5178step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]

def raw5178step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical5178 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5178 = injectiveMoment H node232 := by
  clear _hH
  calc
    injectiveMoment H raw5178 = injectiveMoment H raw5178step0 := by
      have hz : ∀ j, raw5178 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw5178step0 = (fun i j => raw5178 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5178 permutation202 hz
    injectiveMoment H raw5178step0 = injectiveMoment H raw5178step1 := by
      have heq : raw5178step1 = (fun i j => raw5178step0 (permutation45 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5178step0 permutation45 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw5179 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![0, 0]]

def raw5179step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5179step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical5179 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5179 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5179 = injectiveMoment H raw5179step0 := by
      have hz : ∀ j, raw5179 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5179step0 = (fun i j => raw5179 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5179 permutation128 hz
    injectiveMoment H raw5179step0 = injectiveMoment H raw5179step1 := by
      have hz : ∀ j, raw5179step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5179step1 = (fun i j => raw5179step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5179step0 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

def raw5180 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![0, 0], ![0, 0]]

def raw5180step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![0, 0]]

def raw5180step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw5180step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical5180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5180 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5180 = injectiveMoment H raw5180step0 := by
      have hz : ∀ j, raw5180 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw5180step0 = (fun i j => raw5180 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5180 permutation308 hz
    injectiveMoment H raw5180step0 = injectiveMoment H raw5180step1 := by
      have hz : ∀ j, raw5180step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5180step1 = (fun i j => raw5180step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5180step0 permutation128 hz
    injectiveMoment H raw5180step1 = injectiveMoment H raw5180step2 := by
      have hz : ∀ j, raw5180step1 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5180step2 = (fun i j => raw5180step1 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5180step1 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

def raw5181 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]

def raw5181step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]

def raw5181step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical5181 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5181 = injectiveMoment H node232 := by
  clear _hH
  calc
    injectiveMoment H raw5181 = injectiveMoment H raw5181step0 := by
      have hz : ∀ j, raw5181 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw5181step0 = (fun i j => raw5181 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5181 permutation202 hz
    injectiveMoment H raw5181step0 = injectiveMoment H raw5181step1 := by
      have heq : raw5181step1 = (fun i j => raw5181step0 (permutation51 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5181step0 permutation51 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw5182 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![2, -2], ![-1, 1]]

def raw5182step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![2, -2], ![-1, 1]]

def raw5182step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5182 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5182 = injectiveMoment H node46 := by
  clear _hH
  calc
    injectiveMoment H raw5182 = injectiveMoment H raw5182step0 := by
      have hz : ∀ j, raw5182 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw5182step0 = (fun i j => raw5182 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5182 permutation57 hz
    injectiveMoment H raw5182step0 = injectiveMoment H raw5182step1 := by
      have heq : raw5182step1 = (fun i j => raw5182step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5182step0 permutation13 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5183 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2]]

def raw5183step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical5183 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5183 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5183 = injectiveMoment H raw5183step0 := by
      have hz : ∀ j, raw5183 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5183step0 = (fun i j => raw5183 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5183 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
