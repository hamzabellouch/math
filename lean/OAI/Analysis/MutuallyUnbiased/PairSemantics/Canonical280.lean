import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8960 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]

def raw8960step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8960step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8960 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8960 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8960 = injectiveMoment H raw8960step0 := by
      have hz : ∀ j, raw8960 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw8960step0 = (fun i j => raw8960 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8960 permutation258 hz
    injectiveMoment H raw8960step0 = injectiveMoment H raw8960step1 := by
      have hz : ∀ j, raw8960step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8960step1 = (fun i j => raw8960step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8960step0 permutation33 hz
    _ = injectiveMoment H node46 := by rfl

def raw8961 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def raw8961step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical8961 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8961 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw8961 = injectiveMoment H raw8961step0 := by
      have hz : ∀ j, raw8961 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw8961step0 = (fun i j => raw8961 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8961 permutation151 hz
    _ = injectiveMoment H node232 := by rfl

def raw8962 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8962step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8962 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8962 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8962 = injectiveMoment H raw8962step0 := by
      have hz : ∀ j, raw8962 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8962step0 = (fun i j => raw8962 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8962 permutation33 hz
    _ = injectiveMoment H node46 := by rfl

def raw8963 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![0, 0]]

def raw8963step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

def raw8963step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8963 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8963 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8963 = injectiveMoment H raw8963step0 := by
      have hz : ∀ j, raw8963 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw8963step0 = (fun i j => raw8963 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8963 permutation308 hz
    injectiveMoment H raw8963step0 = injectiveMoment H raw8963step1 := by
      have hz : ∀ j, raw8963step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8963step1 = (fun i j => raw8963step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8963step0 permutation33 hz
    _ = injectiveMoment H node46 := by rfl

def raw8964 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw8964step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw8964step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8964 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8964 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8964 = injectiveMoment H raw8964step0 := by
      have hz : ∀ j, raw8964 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8964step0 = (fun i j => raw8964 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8964 permutation33 hz
    injectiveMoment H raw8964step0 = injectiveMoment H raw8964step1 := by
      have heq : raw8964step1 = (fun i j => raw8964step0 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8964step0 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw8965 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![2, -2], ![1, -1], ![0, 0]]

def raw8965step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw8965step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw8965step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8965 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8965 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8965 = injectiveMoment H raw8965step0 := by
      have hz : ∀ j, raw8965 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw8965step0 = (fun i j => raw8965 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8965 permutation308 hz
    injectiveMoment H raw8965step0 = injectiveMoment H raw8965step1 := by
      have hz : ∀ j, raw8965step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8965step1 = (fun i j => raw8965step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8965step0 permutation33 hz
    injectiveMoment H raw8965step1 = injectiveMoment H raw8965step2 := by
      have heq : raw8965step2 = (fun i j => raw8965step1 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8965step1 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw8966 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![3, -3]]

def raw8966step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw8966step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical8966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8966 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw8966 = injectiveMoment H raw8966step0 := by
      have hz : ∀ j, raw8966 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8966step0 = (fun i j => raw8966 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8966 permutation9 hz
    injectiveMoment H raw8966step0 = injectiveMoment H raw8966step1 := by
      have heq : raw8966step1 = (fun i j => raw8966step0 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8966step0 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw8967 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![-1, 1], ![3, -3]]

def raw8967step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![3, -3]]

def raw8967step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw8967step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical8967 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8967 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw8967 = injectiveMoment H raw8967step0 := by
      have hz : ∀ j, raw8967 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw8967step0 = (fun i j => raw8967 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8967 permutation80 hz
    injectiveMoment H raw8967step0 = injectiveMoment H raw8967step1 := by
      have hz : ∀ j, raw8967step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8967step1 = (fun i j => raw8967step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8967step0 permutation9 hz
    injectiveMoment H raw8967step1 = injectiveMoment H raw8967step2 := by
      have heq : raw8967step2 = (fun i j => raw8967step1 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8967step1 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw8968 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![2, -2]]

def raw8968step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def raw8968step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![2, -2]]

def raw8968step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw8968step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical8968 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8968 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8968 = injectiveMoment H raw8968step0 := by
      have hz : ∀ j, raw8968 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw8968step0 = (fun i j => raw8968 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8968 permutation258 hz
    injectiveMoment H raw8968step0 = injectiveMoment H raw8968step1 := by
      have hz : ∀ j, raw8968step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw8968step1 = (fun i j => raw8968step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8968step0 permutation104 hz
    injectiveMoment H raw8968step1 = injectiveMoment H raw8968step2 := by
      have hz : ∀ j, raw8968step1 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw8968step2 = (fun i j => raw8968step1 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8968step1 permutation21 hz
    injectiveMoment H raw8968step2 = injectiveMoment H raw8968step3 := by
      have hz : ∀ j, raw8968step2 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8968step3 = (fun i j => raw8968step2 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8968step2 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

def raw8969 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def raw8969step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![2, -2]]

def raw8969step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw8969step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical8969 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8969 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8969 = injectiveMoment H raw8969step0 := by
      have hz : ∀ j, raw8969 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw8969step0 = (fun i j => raw8969 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8969 permutation104 hz
    injectiveMoment H raw8969step0 = injectiveMoment H raw8969step1 := by
      have hz : ∀ j, raw8969step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw8969step1 = (fun i j => raw8969step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8969step0 permutation21 hz
    injectiveMoment H raw8969step1 = injectiveMoment H raw8969step2 := by
      have hz : ∀ j, raw8969step1 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8969step2 = (fun i j => raw8969step1 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8969step1 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

def raw8970 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![0, 0]]

def raw8970step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![0, 0], ![2, -2]]

def raw8970step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![2, -2]]

def raw8970step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw8970step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical8970 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8970 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8970 = injectiveMoment H raw8970step0 := by
      have hz : ∀ j, raw8970 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw8970step0 = (fun i j => raw8970 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8970 permutation308 hz
    injectiveMoment H raw8970step0 = injectiveMoment H raw8970step1 := by
      have hz : ∀ j, raw8970step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw8970step1 = (fun i j => raw8970step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8970step0 permutation104 hz
    injectiveMoment H raw8970step1 = injectiveMoment H raw8970step2 := by
      have hz : ∀ j, raw8970step1 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw8970step2 = (fun i j => raw8970step1 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8970step1 permutation21 hz
    injectiveMoment H raw8970step2 = injectiveMoment H raw8970step3 := by
      have hz : ∀ j, raw8970step2 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8970step3 = (fun i j => raw8970step2 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8970step2 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

def raw8971 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![1, -1], ![1, -1]]

def raw8971step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw8971step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical8971 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8971 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw8971 = injectiveMoment H raw8971step0 := by
      have hz : ∀ j, raw8971 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw8971step0 = (fun i j => raw8971 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8971 permutation80 hz
    injectiveMoment H raw8971step0 = injectiveMoment H raw8971step1 := by
      have hz : ∀ j, raw8971step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8971step1 = (fun i j => raw8971step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8971step0 permutation9 hz
    _ = injectiveMoment H node11 := by rfl

def raw8972 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![2, -2]]

def raw8972step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw8972step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical8972 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8972 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8972 = injectiveMoment H raw8972step0 := by
      have hz : ∀ j, raw8972 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw8972step0 = (fun i j => raw8972 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8972 permutation21 hz
    injectiveMoment H raw8972step0 = injectiveMoment H raw8972step1 := by
      have hz : ∀ j, raw8972step0 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8972step1 = (fun i j => raw8972step0 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8972step0 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

def raw8973 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![2, -2], ![0, 0]]

def raw8973step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![2, -2]]

def raw8973step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw8973step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical8973 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8973 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8973 = injectiveMoment H raw8973step0 := by
      have hz : ∀ j, raw8973 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8973step0 = (fun i j => raw8973 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8973 permutation128 hz
    injectiveMoment H raw8973step0 = injectiveMoment H raw8973step1 := by
      have hz : ∀ j, raw8973step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw8973step1 = (fun i j => raw8973step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8973step0 permutation21 hz
    injectiveMoment H raw8973step1 = injectiveMoment H raw8973step2 := by
      have hz : ∀ j, raw8973step1 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8973step2 = (fun i j => raw8973step1 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8973step1 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

def raw8974 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw8974step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw8974step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8974 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8974 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8974 = injectiveMoment H raw8974step0 := by
      have hz : ∀ j, raw8974 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8974step0 = (fun i j => raw8974 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8974 permutation33 hz
    injectiveMoment H raw8974step0 = injectiveMoment H raw8974step1 := by
      have heq : raw8974step1 = (fun i j => raw8974step0 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8974step0 permutation11 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw8975 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![-1, 1], ![2, -2], ![0, 0]]

def raw8975step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw8975step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw8975step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8975 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8975 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8975 = injectiveMoment H raw8975step0 := by
      have hz : ∀ j, raw8975 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw8975step0 = (fun i j => raw8975 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8975 permutation308 hz
    injectiveMoment H raw8975step0 = injectiveMoment H raw8975step1 := by
      have hz : ∀ j, raw8975step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8975step1 = (fun i j => raw8975step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8975step0 permutation33 hz
    injectiveMoment H raw8975step1 = injectiveMoment H raw8975step2 := by
      have heq : raw8975step2 = (fun i j => raw8975step1 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8975step1 permutation11 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw8976 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![0, 0], ![-1, 1], ![2, -2]]

def raw8976step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw8976step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]

def raw8976step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8976 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8976 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8976 = injectiveMoment H raw8976step0 := by
      have hz : ∀ j, raw8976 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw8976step0 = (fun i j => raw8976 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8976 permutation241 hz
    injectiveMoment H raw8976step0 = injectiveMoment H raw8976step1 := by
      have hz : ∀ j, raw8976step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8976step1 = (fun i j => raw8976step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8976step0 permutation33 hz
    injectiveMoment H raw8976step1 = injectiveMoment H raw8976step2 := by
      have heq : raw8976step2 = (fun i j => raw8976step1 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8976step1 permutation11 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw8977 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![1, -1]]

def raw8977step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![0, 0], ![1, -1]]

def raw8977step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw8977step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical8977 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8977 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw8977 = injectiveMoment H raw8977step0 := by
      have hz : ∀ j, raw8977 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw8977step0 = (fun i j => raw8977 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8977 permutation258 hz
    injectiveMoment H raw8977step0 = injectiveMoment H raw8977step1 := by
      have hz : ∀ j, raw8977step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw8977step1 = (fun i j => raw8977step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8977step0 permutation104 hz
    injectiveMoment H raw8977step1 = injectiveMoment H raw8977step2 := by
      have hz : ∀ j, raw8977step1 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8977step2 = (fun i j => raw8977step1 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8977step1 permutation9 hz
    _ = injectiveMoment H node11 := by rfl

def raw8978 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![0, 0], ![1, -1]]

def raw8978step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw8978step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical8978 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8978 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw8978 = injectiveMoment H raw8978step0 := by
      have hz : ∀ j, raw8978 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw8978step0 = (fun i j => raw8978 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8978 permutation104 hz
    injectiveMoment H raw8978step0 = injectiveMoment H raw8978step1 := by
      have hz : ∀ j, raw8978step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8978step1 = (fun i j => raw8978step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8978step0 permutation9 hz
    _ = injectiveMoment H node11 := by rfl

def raw8979 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw8979step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical8979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8979 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw8979 = injectiveMoment H raw8979step0 := by
      have hz : ∀ j, raw8979 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8979step0 = (fun i j => raw8979 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8979 permutation9 hz
    _ = injectiveMoment H node11 := by rfl

def raw8980 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]

def raw8980step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]

def raw8980step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical8980 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8980 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw8980 = injectiveMoment H raw8980step0 := by
      have hz : ∀ j, raw8980 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw8980step0 = (fun i j => raw8980 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8980 permutation151 hz
    injectiveMoment H raw8980step0 = injectiveMoment H raw8980step1 := by
      have heq : raw8980step1 = (fun i j => raw8980step0 (permutation45 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8980step0 permutation45 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw8981 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1], ![0, 0]]

def raw8981step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw8981step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical8981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8981 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw8981 = injectiveMoment H raw8981step0 := by
      have hz : ∀ j, raw8981 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8981step0 = (fun i j => raw8981 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8981 permutation128 hz
    injectiveMoment H raw8981step0 = injectiveMoment H raw8981step1 := by
      have hz : ∀ j, raw8981step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8981step1 = (fun i j => raw8981step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8981step0 permutation9 hz
    _ = injectiveMoment H node11 := by rfl

def raw8982 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1], ![0, 0], ![0, 0]]

def raw8982step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1], ![0, 0]]

def raw8982step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1]]

def raw8982step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical8982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8982 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw8982 = injectiveMoment H raw8982step0 := by
      have hz : ∀ j, raw8982 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw8982step0 = (fun i j => raw8982 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8982 permutation308 hz
    injectiveMoment H raw8982step0 = injectiveMoment H raw8982step1 := by
      have hz : ∀ j, raw8982step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8982step1 = (fun i j => raw8982step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8982step0 permutation128 hz
    injectiveMoment H raw8982step1 = injectiveMoment H raw8982step2 := by
      have hz : ∀ j, raw8982step1 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8982step2 = (fun i j => raw8982step1 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8982step1 permutation9 hz
    _ = injectiveMoment H node11 := by rfl

def raw8983 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]

def raw8983step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]

def raw8983step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical8983 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8983 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw8983 = injectiveMoment H raw8983step0 := by
      have hz : ∀ j, raw8983 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw8983step0 = (fun i j => raw8983 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8983 permutation151 hz
    injectiveMoment H raw8983step0 = injectiveMoment H raw8983step1 := by
      have heq : raw8983step1 = (fun i j => raw8983step0 (permutation51 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8983step0 permutation51 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw8984 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![2, -2], ![-1, 1]]

def raw8984step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![2, -2], ![-1, 1]]

def raw8984step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8984 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8984 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8984 = injectiveMoment H raw8984step0 := by
      have hz : ∀ j, raw8984 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8984step0 = (fun i j => raw8984 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8984 permutation33 hz
    injectiveMoment H raw8984step0 = injectiveMoment H raw8984step1 := by
      have heq : raw8984step1 = (fun i j => raw8984step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8984step0 permutation13 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw8985 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw8985step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical8985 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8985 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8985 = injectiveMoment H raw8985step0 := by
      have hz : ∀ j, raw8985 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8985step0 = (fun i j => raw8985 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8985 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

def raw8986 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2], ![-1, 1], ![1, -1]]

def raw8986step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![-1, 1], ![1, -1]]

def raw8986step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8986 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8986 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8986 = injectiveMoment H raw8986step0 := by
      have hz : ∀ j, raw8986 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8986step0 = (fun i j => raw8986 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8986 permutation33 hz
    injectiveMoment H raw8986step0 = injectiveMoment H raw8986step1 := by
      have heq : raw8986step1 = (fun i j => raw8986step0 (permutation12 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8986step0 permutation12 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw8987 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2], ![0, 0]]

def raw8987step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw8987step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical8987 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8987 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8987 = injectiveMoment H raw8987step0 := by
      have hz : ∀ j, raw8987 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw8987step0 = (fun i j => raw8987 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8987 permutation27 hz
    injectiveMoment H raw8987step0 = injectiveMoment H raw8987step1 := by
      have hz : ∀ j, raw8987step0 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8987step1 = (fun i j => raw8987step0 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8987step0 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

def raw8988 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2], ![0, 0], ![0, 0]]

def raw8988step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2], ![0, 0]]

def raw8988step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw8988step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical8988 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8988 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8988 = injectiveMoment H raw8988step0 := by
      have hz : ∀ j, raw8988 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8988step0 = (fun i j => raw8988 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8988 permutation128 hz
    injectiveMoment H raw8988step0 = injectiveMoment H raw8988step1 := by
      have hz : ∀ j, raw8988step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw8988step1 = (fun i j => raw8988step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8988step0 permutation27 hz
    injectiveMoment H raw8988step1 = injectiveMoment H raw8988step2 := by
      have hz : ∀ j, raw8988step1 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8988step2 = (fun i j => raw8988step1 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8988step1 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

def raw8989 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2], ![0, 0], ![0, 0], ![0, 0]]

def raw8989step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2], ![0, 0], ![0, 0]]

def raw8989step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2], ![0, 0]]

def raw8989step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2]]

def raw8989step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical8989 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8989 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8989 = injectiveMoment H raw8989step0 := by
      have hz : ∀ j, raw8989 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw8989step0 = (fun i j => raw8989 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8989 permutation308 hz
    injectiveMoment H raw8989step0 = injectiveMoment H raw8989step1 := by
      have hz : ∀ j, raw8989step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8989step1 = (fun i j => raw8989step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8989step0 permutation128 hz
    injectiveMoment H raw8989step1 = injectiveMoment H raw8989step2 := by
      have hz : ∀ j, raw8989step1 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw8989step2 = (fun i j => raw8989step1 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8989step1 permutation27 hz
    injectiveMoment H raw8989step2 = injectiveMoment H raw8989step3 := by
      have hz : ∀ j, raw8989step2 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8989step3 = (fun i j => raw8989step2 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8989step2 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

def raw8990 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2], ![1, -1], ![0, 0], ![-1, 1]]

def raw8990step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![2, -2], ![1, -1], ![-1, 1]]

def raw8990step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![1, -1], ![-1, 1]]

def raw8990step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8990 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8990 = injectiveMoment H raw8990step0 := by
      have hz : ∀ j, raw8990 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw8990step0 = (fun i j => raw8990 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8990 permutation258 hz
    injectiveMoment H raw8990step0 = injectiveMoment H raw8990step1 := by
      have hz : ∀ j, raw8990step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8990step1 = (fun i j => raw8990step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8990step0 permutation33 hz
    injectiveMoment H raw8990step1 = injectiveMoment H raw8990step2 := by
      have heq : raw8990step2 = (fun i j => raw8990step1 (permutation14 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8990step1 permutation14 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw8991 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![0, 0], ![2, -2], ![1, -1]]

def raw8991step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw8991step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw8991step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8991 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8991 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8991 = injectiveMoment H raw8991step0 := by
      have hz : ∀ j, raw8991 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw8991step0 = (fun i j => raw8991 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8991 permutation241 hz
    injectiveMoment H raw8991step0 = injectiveMoment H raw8991step1 := by
      have hz : ∀ j, raw8991step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8991step1 = (fun i j => raw8991step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8991step0 permutation33 hz
    injectiveMoment H raw8991step1 = injectiveMoment H raw8991step2 := by
      have heq : raw8991step2 = (fun i j => raw8991step1 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8991step1 permutation16 permutation1
    _ = injectiveMoment H node46 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
