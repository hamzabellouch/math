import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8992 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![0, 0], ![3, -3]]

def raw8992step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![3, -3]]

def raw8992step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw8992step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical8992 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8992 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw8992 = injectiveMoment H raw8992step0 := by
      have hz : ∀ j, raw8992 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw8992step0 = (fun i j => raw8992 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8992 permutation104 hz
    injectiveMoment H raw8992step0 = injectiveMoment H raw8992step1 := by
      have hz : ∀ j, raw8992step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8992step1 = (fun i j => raw8992step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8992step0 permutation9 hz
    injectiveMoment H raw8992step1 = injectiveMoment H raw8992step2 := by
      have heq : raw8992step2 = (fun i j => raw8992step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8992step1 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw8993 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]

def raw8993step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw8993step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw8993step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8993 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8993 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8993 = injectiveMoment H raw8993step0 := by
      have hz : ∀ j, raw8993 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw8993step0 = (fun i j => raw8993 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8993 permutation258 hz
    injectiveMoment H raw8993step0 = injectiveMoment H raw8993step1 := by
      have hz : ∀ j, raw8993step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8993step1 = (fun i j => raw8993step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8993step0 permutation33 hz
    injectiveMoment H raw8993step1 = injectiveMoment H raw8993step2 := by
      have heq : raw8993step2 = (fun i j => raw8993step1 (permutation15 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8993step1 permutation15 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw8994 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw8994step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]

def raw8994step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical8994 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8994 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw8994 = injectiveMoment H raw8994step0 := by
      have hz : ∀ j, raw8994 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw8994step0 = (fun i j => raw8994 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8994 permutation151 hz
    injectiveMoment H raw8994step0 = injectiveMoment H raw8994step1 := by
      have heq : raw8994step1 = (fun i j => raw8994step0 (permutation57 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8994step0 permutation57 permutation1
    _ = injectiveMoment H node232 := by rfl

def raw8995 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw8995step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw8995step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8995 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8995 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8995 = injectiveMoment H raw8995step0 := by
      have hz : ∀ j, raw8995 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8995step0 = (fun i j => raw8995 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8995 permutation33 hz
    injectiveMoment H raw8995step0 = injectiveMoment H raw8995step1 := by
      have heq : raw8995step1 = (fun i j => raw8995step0 (permutation15 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8995step0 permutation15 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw8996 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2], ![0, 0]]

def raw8996step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw8996step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]

def raw8996step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8996 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8996 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8996 = injectiveMoment H raw8996step0 := by
      have hz : ∀ j, raw8996 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw8996step0 = (fun i j => raw8996 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8996 permutation308 hz
    injectiveMoment H raw8996step0 = injectiveMoment H raw8996step1 := by
      have hz : ∀ j, raw8996step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8996step1 = (fun i j => raw8996step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8996step0 permutation33 hz
    injectiveMoment H raw8996step1 = injectiveMoment H raw8996step2 := by
      have heq : raw8996step2 = (fun i j => raw8996step1 (permutation15 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8996step1 permutation15 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw8997 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![2, -2], ![0, 0], ![1, -1]]

def raw8997step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw8997step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw8997step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8997 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8997 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8997 = injectiveMoment H raw8997step0 := by
      have hz : ∀ j, raw8997 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw8997step0 = (fun i j => raw8997 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8997 permutation258 hz
    injectiveMoment H raw8997step0 = injectiveMoment H raw8997step1 := by
      have hz : ∀ j, raw8997step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8997step1 = (fun i j => raw8997step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8997step0 permutation33 hz
    injectiveMoment H raw8997step1 = injectiveMoment H raw8997step2 := by
      have heq : raw8997step2 = (fun i j => raw8997step1 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8997step1 permutation16 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw8998 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw8998step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw8998step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8998 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8998 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8998 = injectiveMoment H raw8998step0 := by
      have hz : ∀ j, raw8998 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8998step0 = (fun i j => raw8998 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8998 permutation33 hz
    injectiveMoment H raw8998step0 = injectiveMoment H raw8998step1 := by
      have heq : raw8998step1 = (fun i j => raw8998step0 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8998step0 permutation16 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw8999 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![2, -2], ![1, -1], ![0, 0]]

def raw8999step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw8999step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]

def raw8999step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8999 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8999 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8999 = injectiveMoment H raw8999step0 := by
      have hz : ∀ j, raw8999 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw8999step0 = (fun i j => raw8999 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8999 permutation308 hz
    injectiveMoment H raw8999step0 = injectiveMoment H raw8999step1 := by
      have hz : ∀ j, raw8999step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8999step1 = (fun i j => raw8999step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8999step0 permutation33 hz
    injectiveMoment H raw8999step1 = injectiveMoment H raw8999step2 := by
      have heq : raw8999step2 = (fun i j => raw8999step1 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8999step1 permutation16 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw9000 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![3, -3]]

def raw9000step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw9000step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical9000 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9000 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw9000 = injectiveMoment H raw9000step0 := by
      have hz : ∀ j, raw9000 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9000step0 = (fun i j => raw9000 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9000 permutation9 hz
    injectiveMoment H raw9000step0 = injectiveMoment H raw9000step1 := by
      have heq : raw9000step1 = (fun i j => raw9000step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9000step0 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw9001 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![3, -3]]

def raw9001step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw9001step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw9001step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical9001 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9001 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw9001 = injectiveMoment H raw9001step0 := by
      have hz : ∀ j, raw9001 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw9001step0 = (fun i j => raw9001 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9001 permutation258 hz
    injectiveMoment H raw9001step0 = injectiveMoment H raw9001step1 := by
      have hz : ∀ j, raw9001step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9001step1 = (fun i j => raw9001step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9001step0 permutation33 hz
    injectiveMoment H raw9001step1 = injectiveMoment H raw9001step2 := by
      have heq : raw9001step2 = (fun i j => raw9001step1 (permutation27 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9001step1 permutation27 permutation2
    _ = injectiveMoment H node26 := by rfl

def raw9002 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw9002step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]

def raw9002step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical9002 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9002 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw9002 = injectiveMoment H raw9002step0 := by
      have hz : ∀ j, raw9002 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9002step0 = (fun i j => raw9002 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9002 permutation151 hz
    injectiveMoment H raw9002step0 = injectiveMoment H raw9002step1 := by
      have heq : raw9002step1 = (fun i j => raw9002step0 (permutation145 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9002step0 permutation145 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw9003 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw9003step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]

def raw9003step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical9003 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9003 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw9003 = injectiveMoment H raw9003step0 := by
      have hz : ∀ j, raw9003 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9003step0 = (fun i j => raw9003 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9003 permutation151 hz
    injectiveMoment H raw9003step0 = injectiveMoment H raw9003step1 := by
      have heq : raw9003step1 = (fun i j => raw9003step0 (permutation122 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9003step0 permutation122 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw9004 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw9004step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw9004step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical9004 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9004 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw9004 = injectiveMoment H raw9004step0 := by
      have hz : ∀ j, raw9004 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9004step0 = (fun i j => raw9004 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9004 permutation33 hz
    injectiveMoment H raw9004step0 = injectiveMoment H raw9004step1 := by
      have heq : raw9004step1 = (fun i j => raw9004step0 (permutation27 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9004step0 permutation27 permutation2
    _ = injectiveMoment H node26 := by rfl

def raw9005 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![3, -3]]

def raw9005step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw9005step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]

def raw9005step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical9005 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9005 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw9005 = injectiveMoment H raw9005step0 := by
      have hz : ∀ j, raw9005 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw9005step0 = (fun i j => raw9005 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9005 permutation241 hz
    injectiveMoment H raw9005step0 = injectiveMoment H raw9005step1 := by
      have hz : ∀ j, raw9005step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9005step1 = (fun i j => raw9005step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9005step0 permutation33 hz
    injectiveMoment H raw9005step1 = injectiveMoment H raw9005step2 := by
      have heq : raw9005step2 = (fun i j => raw9005step1 (permutation27 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9005step1 permutation27 permutation2
    _ = injectiveMoment H node26 := by rfl

def raw9006 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![2, -2]]

def raw9006step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw9006step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9006step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9006step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9006 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9006 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9006 = injectiveMoment H raw9006step0 := by
      have hz : ∀ j, raw9006 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw9006step0 = (fun i j => raw9006 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9006 permutation258 hz
    injectiveMoment H raw9006step0 = injectiveMoment H raw9006step1 := by
      have hz : ∀ j, raw9006step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw9006step1 = (fun i j => raw9006step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9006step0 permutation104 hz
    injectiveMoment H raw9006step1 = injectiveMoment H raw9006step2 := by
      have hz : ∀ j, raw9006step1 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9006step2 = (fun i j => raw9006step1 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9006step1 permutation9 hz
    injectiveMoment H raw9006step2 = injectiveMoment H raw9006step3 := by
      have heq : raw9006step3 = (fun i j => raw9006step2 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9006step2 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw9007 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]

def raw9007step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9007step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical9007 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9007 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw9007 = injectiveMoment H raw9007step0 := by
      have hz : ∀ j, raw9007 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw9007step0 = (fun i j => raw9007 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9007 permutation241 hz
    injectiveMoment H raw9007step0 = injectiveMoment H raw9007step1 := by
      have hz : ∀ j, raw9007step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9007step1 = (fun i j => raw9007step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9007step0 permutation33 hz
    _ = injectiveMoment H node65 := by rfl

def raw9008 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw9008step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9008step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9008step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9008 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9008 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9008 = injectiveMoment H raw9008step0 := by
      have hz : ∀ j, raw9008 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw9008step0 = (fun i j => raw9008 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9008 permutation104 hz
    injectiveMoment H raw9008step0 = injectiveMoment H raw9008step1 := by
      have hz : ∀ j, raw9008step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9008step1 = (fun i j => raw9008step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9008step0 permutation9 hz
    injectiveMoment H raw9008step1 = injectiveMoment H raw9008step2 := by
      have heq : raw9008step2 = (fun i j => raw9008step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9008step1 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw9009 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2], ![0, 0]]

def raw9009step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]

def raw9009step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9009step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9009step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9009 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9009 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9009 = injectiveMoment H raw9009step0 := by
      have hz : ∀ j, raw9009 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw9009step0 = (fun i j => raw9009 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9009 permutation308 hz
    injectiveMoment H raw9009step0 = injectiveMoment H raw9009step1 := by
      have hz : ∀ j, raw9009step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw9009step1 = (fun i j => raw9009step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9009step0 permutation104 hz
    injectiveMoment H raw9009step1 = injectiveMoment H raw9009step2 := by
      have hz : ∀ j, raw9009step1 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9009step2 = (fun i j => raw9009step1 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9009step1 permutation9 hz
    injectiveMoment H raw9009step2 = injectiveMoment H raw9009step3 := by
      have heq : raw9009step3 = (fun i j => raw9009step2 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9009step2 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw9010 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![1, -1]]

def raw9010step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9010step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical9010 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9010 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw9010 = injectiveMoment H raw9010step0 := by
      have hz : ∀ j, raw9010 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw9010step0 = (fun i j => raw9010 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9010 permutation258 hz
    injectiveMoment H raw9010step0 = injectiveMoment H raw9010step1 := by
      have hz : ∀ j, raw9010step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9010step1 = (fun i j => raw9010step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9010step0 permutation33 hz
    _ = injectiveMoment H node65 := by rfl

def raw9011 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9011step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical9011 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9011 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw9011 = injectiveMoment H raw9011step0 := by
      have hz : ∀ j, raw9011 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9011step0 = (fun i j => raw9011 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9011 permutation33 hz
    _ = injectiveMoment H node65 := by rfl

def raw9012 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![0, 0]]

def raw9012step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

def raw9012step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]

theorem canonical9012 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9012 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw9012 = injectiveMoment H raw9012step0 := by
      have hz : ∀ j, raw9012 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw9012step0 = (fun i j => raw9012 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9012 permutation308 hz
    injectiveMoment H raw9012step0 = injectiveMoment H raw9012step1 := by
      have hz : ∀ j, raw9012step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9012step1 = (fun i j => raw9012step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9012step0 permutation33 hz
    _ = injectiveMoment H node65 := by rfl

def raw9013 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9013step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9013step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9013 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9013 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9013 = injectiveMoment H raw9013step0 := by
      have hz : ∀ j, raw9013 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9013step0 = (fun i j => raw9013 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9013 permutation9 hz
    injectiveMoment H raw9013step0 = injectiveMoment H raw9013step1 := by
      have heq : raw9013step1 = (fun i j => raw9013step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9013step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw9014 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2], ![-1, 1], ![1, -1]]

def raw9014step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![-1, 1], ![1, -1]]

def raw9014step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical9014 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9014 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw9014 = injectiveMoment H raw9014step0 := by
      have hz : ∀ j, raw9014 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9014step0 = (fun i j => raw9014 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9014 permutation151 hz
    injectiveMoment H raw9014step0 = injectiveMoment H raw9014step1 := by
      have heq : raw9014step1 = (fun i j => raw9014step0 (permutation98 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9014step0 permutation98 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw9015 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2], ![0, 0]]

def raw9015step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9015step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9015step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9015 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9015 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9015 = injectiveMoment H raw9015step0 := by
      have hz : ∀ j, raw9015 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw9015step0 = (fun i j => raw9015 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9015 permutation128 hz
    injectiveMoment H raw9015step0 = injectiveMoment H raw9015step1 := by
      have hz : ∀ j, raw9015step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9015step1 = (fun i j => raw9015step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9015step0 permutation9 hz
    injectiveMoment H raw9015step1 = injectiveMoment H raw9015step2 := by
      have heq : raw9015step2 = (fun i j => raw9015step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9015step1 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw9016 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2], ![0, 0], ![0, 0]]

def raw9016step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2], ![0, 0]]

def raw9016step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9016step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9016step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9016 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9016 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9016 = injectiveMoment H raw9016step0 := by
      have hz : ∀ j, raw9016 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw9016step0 = (fun i j => raw9016 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9016 permutation308 hz
    injectiveMoment H raw9016step0 = injectiveMoment H raw9016step1 := by
      have hz : ∀ j, raw9016step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw9016step1 = (fun i j => raw9016step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9016step0 permutation128 hz
    injectiveMoment H raw9016step1 = injectiveMoment H raw9016step2 := by
      have hz : ∀ j, raw9016step1 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9016step2 = (fun i j => raw9016step1 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9016step1 permutation9 hz
    injectiveMoment H raw9016step2 = injectiveMoment H raw9016step3 := by
      have heq : raw9016step3 = (fun i j => raw9016step2 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9016step2 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw9017 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![-1, 1]]

def raw9017step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![-1, 1]]

def raw9017step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical9017 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9017 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw9017 = injectiveMoment H raw9017step0 := by
      have hz : ∀ j, raw9017 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9017step0 = (fun i j => raw9017 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9017 permutation151 hz
    injectiveMoment H raw9017step0 = injectiveMoment H raw9017step1 := by
      have heq : raw9017step1 = (fun i j => raw9017step0 (permutation92 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9017step0 permutation92 permutation2
    _ = injectiveMoment H node232 := by rfl

def raw9018 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![0, 0], ![-1, 1], ![2, -2]]

def raw9018step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9018step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]

def raw9018step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical9018 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9018 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9018 = injectiveMoment H raw9018step0 := by
      have hz : ∀ j, raw9018 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw9018step0 = (fun i j => raw9018 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9018 permutation80 hz
    injectiveMoment H raw9018step0 = injectiveMoment H raw9018step1 := by
      have hz : ∀ j, raw9018step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9018step1 = (fun i j => raw9018step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9018step0 permutation9 hz
    injectiveMoment H raw9018step1 = injectiveMoment H raw9018step2 := by
      have heq : raw9018step2 = (fun i j => raw9018step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9018step1 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

def raw9019 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![0, 0], ![0, 0], ![1, -1]]

def raw9019step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![0, 0], ![1, -1]]

def raw9019step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def raw9019step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical9019 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9019 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw9019 = injectiveMoment H raw9019step0 := by
      have hz : ∀ j, raw9019 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw9019step0 = (fun i j => raw9019 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9019 permutation104 hz
    injectiveMoment H raw9019step0 = injectiveMoment H raw9019step1 := by
      have hz : ∀ j, raw9019step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw9019step1 = (fun i j => raw9019step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9019step0 permutation21 hz
    injectiveMoment H raw9019step1 = injectiveMoment H raw9019step2 := by
      have hz : ∀ j, raw9019step1 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9019step2 = (fun i j => raw9019step1 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9019step1 permutation3 hz
    _ = injectiveMoment H node5 := by rfl

def raw9020 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![0, 0], ![1, -1]]

def raw9020step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def raw9020step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical9020 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9020 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw9020 = injectiveMoment H raw9020step0 := by
      have hz : ∀ j, raw9020 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw9020step0 = (fun i j => raw9020 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9020 permutation21 hz
    injectiveMoment H raw9020step0 = injectiveMoment H raw9020step1 := by
      have hz : ∀ j, raw9020step0 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9020step1 = (fun i j => raw9020step0 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9020step0 permutation3 hz
    _ = injectiveMoment H node5 := by rfl

def raw9021 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1]]

def raw9021step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

theorem canonical9021 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9021 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw9021 = injectiveMoment H raw9021step0 := by
      have hz : ∀ j, raw9021 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9021step0 = (fun i j => raw9021 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9021 permutation3 hz
    _ = injectiveMoment H node5 := by rfl

def raw9022 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-2, 2], ![0, 0], ![2, -2]]

def raw9022step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw9022step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]

def raw9022step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical9022 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9022 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw9022 = injectiveMoment H raw9022step0 := by
      have hz : ∀ j, raw9022 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw9022step0 = (fun i j => raw9022 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9022 permutation258 hz
    injectiveMoment H raw9022step0 = injectiveMoment H raw9022step1 := by
      have hz : ∀ j, raw9022step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9022step1 = (fun i j => raw9022step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9022step0 permutation33 hz
    injectiveMoment H raw9022step1 = injectiveMoment H raw9022step2 := by
      have heq : raw9022step2 = (fun i j => raw9022step1 (permutation21 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9022step1 permutation21 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw9023 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9023step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2]]

def raw9023step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical9023 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9023 = injectiveMoment H node232 := by
  calc
    injectiveMoment H raw9023 = injectiveMoment H raw9023step0 := by
      have hz : ∀ j, raw9023 (permutation151 0) j = 0 := by decide +kernel
      have heq : raw9023step0 = (fun i j => raw9023 (permutation151 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9023 permutation151 hz
    injectiveMoment H raw9023step0 = injectiveMoment H raw9023step1 := by
      have heq : raw9023step1 = (fun i j => raw9023step0 (permutation133 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9023step0 permutation133 permutation2
    _ = injectiveMoment H node232 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
