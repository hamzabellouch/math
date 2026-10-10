import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5184 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![-1, 1], ![1, -1]]

def raw5184step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![-1, 1], ![1, -1]]

def raw5184step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5184 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5184 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5184 = injectiveMoment H raw5184step0 := by
      have hz : ∀ j, raw5184 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw5184step0 = (fun i j => raw5184 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5184 permutation57 hz
    injectiveMoment H raw5184step0 = injectiveMoment H raw5184step1 := by
      have heq : raw5184step1 = (fun i j => raw5184step0 (permutation12 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5184step0 permutation12 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5185 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![0, 0]]

def raw5185step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2]]

def raw5185step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical5185 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5185 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5185 = injectiveMoment H raw5185step0 := by
      have hz : ∀ j, raw5185 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5185step0 = (fun i j => raw5185 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5185 permutation27 hz
    injectiveMoment H raw5185step0 = injectiveMoment H raw5185step1 := by
      have hz : ∀ j, raw5185step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5185step1 = (fun i j => raw5185step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5185step0 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

def raw5186 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![0, 0], ![0, 0], ![0, 0]]

def raw5186step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![0, 0], ![0, 0]]

def raw5186step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![0, 0]]

def raw5186step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2]]

def raw5186step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical5186 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5186 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5186 = injectiveMoment H raw5186step0 := by
      have hz : ∀ j, raw5186 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw5186step0 = (fun i j => raw5186 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5186 permutation308 hz
    injectiveMoment H raw5186step0 = injectiveMoment H raw5186step1 := by
      have hz : ∀ j, raw5186step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5186step1 = (fun i j => raw5186step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5186step0 permutation128 hz
    injectiveMoment H raw5186step1 = injectiveMoment H raw5186step2 := by
      have hz : ∀ j, raw5186step1 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5186step2 = (fun i j => raw5186step1 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5186step1 permutation27 hz
    injectiveMoment H raw5186step2 = injectiveMoment H raw5186step3 := by
      have hz : ∀ j, raw5186step2 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5186step3 = (fun i j => raw5186step2 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5186step2 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

def raw5187 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![1, -1], ![2, -2]]

def raw5187step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical5187 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5187 = injectiveMoment H node231 := by
  calc
    injectiveMoment H raw5187 = injectiveMoment H raw5187step0 := by
      have heq : raw5187step0 = (fun i j => raw5187 (permutation39 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5187 permutation39 permutation1
    _ = injectiveMoment H node231 := by rfl

def raw5188 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]

def raw5188step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]

def raw5188step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical5188 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5188 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw5188 = injectiveMoment H raw5188step0 := by
      have hz : ∀ j, raw5188 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw5188step0 = (fun i j => raw5188 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5188 permutation241 hz
    injectiveMoment H raw5188step0 = injectiveMoment H raw5188step1 := by
      have heq : raw5188step1 = (fun i j => raw5188step0 (permutation39 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5188step0 permutation39 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw5189 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![0, 0], ![2, -2]]

def raw5189step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw5189step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5189 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5189 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5189 = injectiveMoment H raw5189step0 := by
      have hz : ∀ j, raw5189 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5189step0 = (fun i j => raw5189 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5189 permutation104 hz
    injectiveMoment H raw5189step0 = injectiveMoment H raw5189step1 := by
      have heq : raw5189step1 = (fun i j => raw5189step0 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5189step0 permutation11 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5190 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]

def raw5190step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical5190 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5190 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw5190 = injectiveMoment H raw5190step0 := by
      have heq : raw5190step0 = (fun i j => raw5190 (permutation39 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5190 permutation39 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw5191 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1], ![0, 0]]

def raw5191step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]

def raw5191step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical5191 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5191 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw5191 = injectiveMoment H raw5191step0 := by
      have hz : ∀ j, raw5191 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw5191step0 = (fun i j => raw5191 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5191 permutation308 hz
    injectiveMoment H raw5191step0 = injectiveMoment H raw5191step1 := by
      have heq : raw5191step1 = (fun i j => raw5191step0 (permutation39 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5191step0 permutation39 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw5192 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw5192step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5192 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5192 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5192 = injectiveMoment H raw5192step0 := by
      have heq : raw5192step0 = (fun i j => raw5192 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5192 permutation11 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5193 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2], ![0, 0]]

def raw5193step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw5193step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5193 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5193 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5193 = injectiveMoment H raw5193step0 := by
      have hz : ∀ j, raw5193 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5193step0 = (fun i j => raw5193 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5193 permutation128 hz
    injectiveMoment H raw5193step0 = injectiveMoment H raw5193step1 := by
      have heq : raw5193step1 = (fun i j => raw5193step0 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5193step0 permutation11 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5194 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-1, 1], ![2, -2]]

def raw5194step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw5194step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5194 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5194 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5194 = injectiveMoment H raw5194step0 := by
      have hz : ∀ j, raw5194 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5194step0 = (fun i j => raw5194 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5194 permutation80 hz
    injectiveMoment H raw5194step0 = injectiveMoment H raw5194step1 := by
      have heq : raw5194step1 = (fun i j => raw5194step0 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5194step0 permutation11 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5195 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![0, 0], ![1, -1]]

def raw5195step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![1, -1]]

def raw5195step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![1, -1]]

def raw5195step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical5195 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5195 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5195 = injectiveMoment H raw5195step0 := by
      have hz : ∀ j, raw5195 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw5195step0 = (fun i j => raw5195 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5195 permutation258 hz
    injectiveMoment H raw5195step0 = injectiveMoment H raw5195step1 := by
      have hz : ∀ j, raw5195step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5195step1 = (fun i j => raw5195step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5195step0 permutation104 hz
    injectiveMoment H raw5195step1 = injectiveMoment H raw5195step2 := by
      have hz : ∀ j, raw5195step1 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5195step2 = (fun i j => raw5195step1 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5195step1 permutation21 hz
    _ = injectiveMoment H node11 := by rfl

def raw5196 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![1, -1]]

def raw5196step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![1, -1]]

def raw5196step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical5196 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5196 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5196 = injectiveMoment H raw5196step0 := by
      have hz : ∀ j, raw5196 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5196step0 = (fun i j => raw5196 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5196 permutation104 hz
    injectiveMoment H raw5196step0 = injectiveMoment H raw5196step1 := by
      have hz : ∀ j, raw5196step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5196step1 = (fun i j => raw5196step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5196step0 permutation21 hz
    _ = injectiveMoment H node11 := by rfl

def raw5197 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![1, -1]]

def raw5197step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical5197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5197 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5197 = injectiveMoment H raw5197step0 := by
      have hz : ∀ j, raw5197 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5197step0 = (fun i j => raw5197 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5197 permutation21 hz
    _ = injectiveMoment H node11 := by rfl

def raw5198 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![1, -1], ![0, 0]]

def raw5198step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![1, -1]]

def raw5198step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical5198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5198 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5198 = injectiveMoment H raw5198step0 := by
      have hz : ∀ j, raw5198 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5198step0 = (fun i j => raw5198 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5198 permutation128 hz
    injectiveMoment H raw5198step0 = injectiveMoment H raw5198step1 := by
      have hz : ∀ j, raw5198step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5198step1 = (fun i j => raw5198step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5198step0 permutation21 hz
    _ = injectiveMoment H node11 := by rfl

def raw5199 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical5199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5199 = injectiveMoment H node11 := by
  rfl

def raw5200 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-2, 2], ![1, -1], ![1, -1]]

def raw5200step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical5200 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5200 = injectiveMoment H node716 := by
  calc
    injectiveMoment H raw5200 = injectiveMoment H raw5200step0 := by
      have heq : raw5200step0 = (fun i j => raw5200 (permutation176 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5200 permutation176 permutation1
    _ = injectiveMoment H node716 := by rfl

def raw5201 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-2, 2], ![2, -2]]

def raw5201step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical5201 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5201 = injectiveMoment H node231 := by
  calc
    injectiveMoment H raw5201 = injectiveMoment H raw5201step0 := by
      have heq : raw5201step0 = (fun i j => raw5201 (permutation45 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5201 permutation45 permutation1
    _ = injectiveMoment H node231 := by rfl

def raw5202 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![0, 0], ![1, -1]]

def raw5202step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]

def raw5202step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical5202 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5202 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw5202 = injectiveMoment H raw5202step0 := by
      have hz : ∀ j, raw5202 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw5202step0 = (fun i j => raw5202 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5202 permutation258 hz
    injectiveMoment H raw5202step0 = injectiveMoment H raw5202step1 := by
      have heq : raw5202step1 = (fun i j => raw5202step0 (permutation45 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5202step0 permutation45 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw5203 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]

def raw5203step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical5203 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5203 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw5203 = injectiveMoment H raw5203step0 := by
      have heq : raw5203step0 = (fun i j => raw5203 (permutation45 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5203 permutation45 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw5204 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![0, 0]]

def raw5204step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical5204 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5204 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5204 = injectiveMoment H raw5204step0 := by
      have hz : ∀ j, raw5204 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5204step0 = (fun i j => raw5204 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5204 permutation27 hz
    _ = injectiveMoment H node11 := by rfl

def raw5205 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![0, 0], ![0, 0]]

def raw5205step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![0, 0]]

def raw5205step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical5205 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5205 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5205 = injectiveMoment H raw5205step0 := by
      have hz : ∀ j, raw5205 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5205step0 = (fun i j => raw5205 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5205 permutation128 hz
    injectiveMoment H raw5205step0 = injectiveMoment H raw5205step1 := by
      have hz : ∀ j, raw5205step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5205step1 = (fun i j => raw5205step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5205step0 permutation27 hz
    _ = injectiveMoment H node11 := by rfl

def raw5206 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![0, 0], ![0, 0], ![0, 0]]

def raw5206step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![0, 0], ![0, 0]]

def raw5206step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![0, 0]]

def raw5206step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical5206 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5206 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5206 = injectiveMoment H raw5206step0 := by
      have hz : ∀ j, raw5206 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw5206step0 = (fun i j => raw5206 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5206 permutation308 hz
    injectiveMoment H raw5206step0 = injectiveMoment H raw5206step1 := by
      have hz : ∀ j, raw5206step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5206step1 = (fun i j => raw5206step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5206step0 permutation128 hz
    injectiveMoment H raw5206step1 = injectiveMoment H raw5206step2 := by
      have hz : ∀ j, raw5206step1 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5206step2 = (fun i j => raw5206step1 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5206step1 permutation27 hz
    _ = injectiveMoment H node11 := by rfl

def raw5207 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![0, 0], ![-1, 1]]

def raw5207step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]

def raw5207step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical5207 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5207 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw5207 = injectiveMoment H raw5207step0 := by
      have hz : ∀ j, raw5207 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw5207step0 = (fun i j => raw5207 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5207 permutation258 hz
    injectiveMoment H raw5207step0 = injectiveMoment H raw5207step1 := by
      have heq : raw5207step1 = (fun i j => raw5207step0 (permutation51 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5207step0 permutation51 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw5208 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![2, -2], ![-1, 1]]

def raw5208step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5208 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5208 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5208 = injectiveMoment H raw5208step0 := by
      have heq : raw5208step0 = (fun i j => raw5208 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5208 permutation13 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5209 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![2, -2], ![-1, 1], ![0, 0]]

def raw5209step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![2, -2], ![-1, 1]]

def raw5209step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5209 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5209 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5209 = injectiveMoment H raw5209step0 := by
      have hz : ∀ j, raw5209 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5209step0 = (fun i j => raw5209 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5209 permutation128 hz
    injectiveMoment H raw5209step0 = injectiveMoment H raw5209step1 := by
      have heq : raw5209step1 = (fun i j => raw5209step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5209step0 permutation13 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5210 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

def raw5211 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![-2, 2], ![2, -2]]

def raw5211step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]

theorem canonical5211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5211 = injectiveMoment H node45 := by
  calc
    injectiveMoment H raw5211 = injectiveMoment H raw5211step0 := by
      have heq : raw5211step0 = (fun i j => raw5211 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5211 permutation11 permutation1
    _ = injectiveMoment H node45 := by rfl

def raw5212 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![-1, 1], ![0, 0], ![1, -1]]

def raw5212step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![-1, 1], ![1, -1]]

def raw5212step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5212 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5212 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5212 = injectiveMoment H raw5212step0 := by
      have hz : ∀ j, raw5212 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5212step0 = (fun i j => raw5212 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5212 permutation104 hz
    injectiveMoment H raw5212step0 = injectiveMoment H raw5212step1 := by
      have heq : raw5212step1 = (fun i j => raw5212step0 (permutation12 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5212step0 permutation12 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5213 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![-1, 1], ![1, -1]]

def raw5213step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical5213 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5213 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5213 = injectiveMoment H raw5213step0 := by
      have heq : raw5213step0 = (fun i j => raw5213 (permutation12 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5213 permutation12 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw5214 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0]]

def raw5214step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical5214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5214 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5214 = injectiveMoment H raw5214step0 := by
      have hz : ∀ j, raw5214 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw5214step0 = (fun i j => raw5214 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5214 permutation7 hz
    _ = injectiveMoment H node4 := by rfl

def raw5215 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0], ![0, 0]]

def raw5215step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![0, 0]]

def raw5215step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical5215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5215 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5215 = injectiveMoment H raw5215step0 := by
      have hz : ∀ j, raw5215 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5215step0 = (fun i j => raw5215 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5215 permutation27 hz
    injectiveMoment H raw5215step0 = injectiveMoment H raw5215step1 := by
      have hz : ∀ j, raw5215step0 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw5215step1 = (fun i j => raw5215step0 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5215step0 permutation7 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
