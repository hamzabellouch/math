import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4096 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]

def raw4096step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]

def raw4096step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical4096 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4096 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4096 = injectiveMoment H raw4096step0 := by
      have hz : ∀ j, raw4096 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw4096step0 = (fun i j => raw4096 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4096 permutation15 hz
    injectiveMoment H raw4096step0 = injectiveMoment H raw4096step1 := by
      have heq : raw4096step1 = (fun i j => raw4096step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4096step0 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

def raw4097 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw4097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]

def raw4097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]

def raw4097step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4097 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4097 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw4097 = injectiveMoment H raw4097step0 := by
      have heq : raw4097step0 = -raw4097 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4097).symm
    injectiveMoment H raw4097step0 = injectiveMoment H raw4097step1 := by
      have hz : ∀ j, raw4097step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw4097step1 = (fun i j => raw4097step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4097step0 permutation57 hz
    injectiveMoment H raw4097step1 = injectiveMoment H raw4097step2 := by
      have heq : raw4097step2 = (fun i j => raw4097step1 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4097step1 permutation19 permutation5
    _ = injectiveMoment H node203 := by rfl

def raw4098 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw4098step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def raw4098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical4098 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4098 = injectiveMoment H node207 := by
  calc
    injectiveMoment H raw4098 = injectiveMoment H raw4098step0 := by
      have hz : ∀ j, raw4098 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw4098step0 = (fun i j => raw4098 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4098 permutation57 hz
    injectiveMoment H raw4098step0 = injectiveMoment H raw4098step1 := by
      have heq : raw4098step1 = (fun i j => raw4098step0 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4098step0 permutation18 permutation7
    _ = injectiveMoment H node207 := by rfl

def raw4099 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]

def raw4099step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]

theorem canonical4099 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4099 = injectiveMoment H node41 := by
  calc
    injectiveMoment H raw4099 = injectiveMoment H raw4099step0 := by
      have hz : ∀ j, raw4099 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw4099step0 = (fun i j => raw4099 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4099 permutation15 hz
    _ = injectiveMoment H node41 := by rfl

def raw4100 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def raw4100step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical4100 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4100 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw4100 = injectiveMoment H raw4100step0 := by
      have hz : ∀ j, raw4100 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw4100step0 = (fun i j => raw4100 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4100 permutation57 hz
    _ = injectiveMoment H node215 := by rfl

def raw4101 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -3, 2], ![1, 3, -4]]

def raw4101step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -3, 3], ![2, 0, 2, -4]]

def raw4101step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 0, 3, -3], ![-2, 0, -2, 4]]

def raw4101step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![-2, -2, 4]]

def raw4101step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical4101 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4101 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw4101 = injectiveMoment H raw4101step0 := by
      have heq : raw4101step0 = raw4101.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4101).symm
    injectiveMoment H raw4101step0 = injectiveMoment H raw4101step1 := by
      have heq : raw4101step1 = -raw4101step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4101step0).symm
    injectiveMoment H raw4101step1 = injectiveMoment H raw4101step2 := by
      have hz : ∀ i, raw4101step1 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw4101step2 = (fun i j => raw4101step1 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4101step1 permutation15 hz
    injectiveMoment H raw4101step2 = injectiveMoment H raw4101step3 := by
      have heq : raw4101step3 = (fun i j => raw4101step2 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4101step2 permutation8 permutation3
    _ = injectiveMoment H node32 := by rfl

def raw4102 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]

def raw4102step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 2, -1], ![-1, -2, 3]]

def raw4102step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, -2, 3]]

def raw4102step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4102 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4102 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4102 = injectiveMoment H raw4102step0 := by
      have heq : raw4102step0 = -raw4102 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4102).symm
    injectiveMoment H raw4102step0 = injectiveMoment H raw4102step1 := by
      have hz : ∀ j, raw4102step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw4102step1 = (fun i j => raw4102step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4102step0 permutation15 hz
    injectiveMoment H raw4102step1 = injectiveMoment H raw4102step2 := by
      have heq : raw4102step2 = (fun i j => raw4102step1 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4102step1 permutation7 permutation5
    _ = injectiveMoment H node36 := by rfl

def raw4103 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]

def raw4103step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]

def raw4103step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2]]

def raw4103step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical4103 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4103 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4103 = injectiveMoment H raw4103step0 := by
      have heq : raw4103step0 = -raw4103 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4103).symm
    injectiveMoment H raw4103step0 = injectiveMoment H raw4103step1 := by
      have hz : ∀ j, raw4103step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw4103step1 = (fun i j => raw4103step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4103step0 permutation15 hz
    injectiveMoment H raw4103step1 = injectiveMoment H raw4103step2 := by
      have heq : raw4103step2 = (fun i j => raw4103step1 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4103step1 permutation7 permutation5
    _ = injectiveMoment H node62 := by rfl

def raw4104 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]

def raw4104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

theorem canonical4104 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4104 = injectiveMoment H node626 := by
  calc
    injectiveMoment H raw4104 = injectiveMoment H raw4104step0 := by
      have heq : raw4104step0 = (fun i j => raw4104 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4104 permutation39 permutation3
    _ = injectiveMoment H node626 := by rfl

def raw4105 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]

def raw4105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0]]

def raw4105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

theorem canonical4105 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4105 = injectiveMoment H node670 := by
  calc
    injectiveMoment H raw4105 = injectiveMoment H raw4105step0 := by
      have heq : raw4105step0 = -raw4105 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4105).symm
    injectiveMoment H raw4105step0 = injectiveMoment H raw4105step1 := by
      have heq : raw4105step1 = (fun i j => raw4105step0 (permutation50 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4105step0 permutation50 permutation8
    _ = injectiveMoment H node670 := by rfl

def raw4106 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def raw4106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical4106 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4106 = injectiveMoment H node659 := by
  calc
    injectiveMoment H raw4106 = injectiveMoment H raw4106step0 := by
      have heq : raw4106step0 = (fun i j => raw4106 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4106 permutation39 permutation3
    _ = injectiveMoment H node659 := by rfl

def raw4107 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]

def raw4107step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical4107 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4107 = injectiveMoment H node207 := by
  calc
    injectiveMoment H raw4107 = injectiveMoment H raw4107step0 := by
      have hz : ∀ j, raw4107 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw4107step0 = (fun i j => raw4107 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4107 permutation80 hz
    _ = injectiveMoment H node207 := by rfl

def raw4108 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]

def raw4108step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4108 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4108 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw4108 = injectiveMoment H raw4108step0 := by
      have hz : ∀ j, raw4108 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw4108step0 = (fun i j => raw4108 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4108 permutation80 hz
    _ = injectiveMoment H node210 := by rfl

def raw4109 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]

def raw4109step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def raw4109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical4109 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4109 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw4109 = injectiveMoment H raw4109step0 := by
      have hz : ∀ j, raw4109 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw4109step0 = (fun i j => raw4109 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4109 permutation80 hz
    injectiveMoment H raw4109step0 = injectiveMoment H raw4109step1 := by
      have heq : raw4109step1 = (fun i j => raw4109step0 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4109step0 permutation25 permutation6
    _ = injectiveMoment H node294 := by rfl

def raw4110 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]

def raw4110step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]

def raw4110step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical4110 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4110 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4110 = injectiveMoment H raw4110step0 := by
      have hz : ∀ j, raw4110 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw4110step0 = (fun i j => raw4110 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4110 permutation21 hz
    injectiveMoment H raw4110step0 = injectiveMoment H raw4110step1 := by
      have heq : raw4110step1 = (fun i j => raw4110step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4110step0 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

def raw4111 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]

def raw4111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical4111 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4111 = injectiveMoment H node655 := by
  calc
    injectiveMoment H raw4111 = injectiveMoment H raw4111step0 := by
      have heq : raw4111step0 = (fun i j => raw4111 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4111 permutation45 permutation3
    _ = injectiveMoment H node655 := by rfl

def raw4112 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]

def raw4112step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical4112 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4112 = injectiveMoment H node207 := by
  calc
    injectiveMoment H raw4112 = injectiveMoment H raw4112step0 := by
      have hz : ∀ j, raw4112 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw4112step0 = (fun i j => raw4112 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4112 permutation104 hz
    _ = injectiveMoment H node207 := by rfl

def raw4113 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]

def raw4113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 3, -1]]

def raw4113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical4113 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4113 = injectiveMoment H node566 := by
  calc
    injectiveMoment H raw4113 = injectiveMoment H raw4113step0 := by
      have heq : raw4113step0 = -raw4113 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4113).symm
    injectiveMoment H raw4113step0 = injectiveMoment H raw4113step1 := by
      have heq : raw4113step1 = (fun i j => raw4113step0 (permutation136 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4113step0 permutation136 permutation4
    _ = injectiveMoment H node566 := by rfl

def raw4114 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

theorem canonical4114 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4114 = injectiveMoment H node666 := by
  rfl

def raw4115 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

theorem canonical4115 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4115 = injectiveMoment H node667 := by
  rfl

def raw4116 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

theorem canonical4116 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4116 = injectiveMoment H node668 := by
  rfl

def raw4117 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical4117 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4117 = injectiveMoment H node207 := by
  rfl

def raw4118 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![0, -2, 2], ![2, -1, -1]]

def raw4118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical4118 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4118 = injectiveMoment H node642 := by
  calc
    injectiveMoment H raw4118 = injectiveMoment H raw4118step0 := by
      have heq : raw4118step0 = (fun i j => raw4118 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4118 permutation45 permutation3
    _ = injectiveMoment H node642 := by rfl

def raw4119 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0]]

def raw4119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical4119 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4119 = injectiveMoment H node656 := by
  calc
    injectiveMoment H raw4119 = injectiveMoment H raw4119step0 := by
      have heq : raw4119step0 = (fun i j => raw4119 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4119 permutation45 permutation3
    _ = injectiveMoment H node656 := by rfl

def raw4120 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

theorem canonical4120 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4120 = injectiveMoment H node669 := by
  rfl

def raw4121 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

theorem canonical4121 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4121 = injectiveMoment H node670 := by
  rfl

def raw4122 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1]]

def raw4122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

theorem canonical4122 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4122 = injectiveMoment H node670 := by
  calc
    injectiveMoment H raw4122 = injectiveMoment H raw4122step0 := by
      have heq : raw4122step0 = (fun i j => raw4122 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4122 permutation34 permutation3
    _ = injectiveMoment H node670 := by rfl

def raw4123 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]

def raw4123step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 3, -1]]

def raw4123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical4123 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4123 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw4123 = injectiveMoment H raw4123step0 := by
      have heq : raw4123step0 = -raw4123 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4123).symm
    injectiveMoment H raw4123step0 = injectiveMoment H raw4123step1 := by
      have heq : raw4123step1 = (fun i j => raw4123step0 (permutation30 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4123step0 permutation30 permutation4
    _ = injectiveMoment H node177 := by rfl

def raw4124 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 3, -3], ![1, -3, 2], ![1, -1, 0]]

theorem canonical4124 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4124 = injectiveMoment H node671 := by
  rfl

def raw4125 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -2, 1]]

theorem canonical4125 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4125 = injectiveMoment H node672 := by
  rfl

def raw4126 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -4, 3], ![1, 3, -4]]

theorem canonical4126 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4126 = injectiveMoment H node208 := by
  rfl

def raw4127 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical4127 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4127 = injectiveMoment H node209 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
