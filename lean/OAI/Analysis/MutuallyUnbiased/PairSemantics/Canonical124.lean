import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3968 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]

def raw3968step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]

def raw3968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

theorem canonical3968 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3968 = injectiveMoment H node224 := by
  calc
    injectiveMoment H raw3968 = injectiveMoment H raw3968step0 := by
      have hz : ∀ j, raw3968 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw3968step0 = (fun i j => raw3968 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw3968 permutation80 hz
    injectiveMoment H raw3968step0 = injectiveMoment H raw3968step1 := by
      have heq : raw3968step1 = (fun i j => raw3968step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3968step0 permutation22 permutation5
    _ = injectiveMoment H node224 := by rfl

def raw3969 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def raw3969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

theorem canonical3969 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3969 = injectiveMoment H node358 := by
  calc
    injectiveMoment H raw3969 = injectiveMoment H raw3969step0 := by
      have heq : raw3969step0 = (fun i j => raw3969 (permutation109 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3969 permutation109 permutation5
    _ = injectiveMoment H node358 := by rfl

def raw3970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical3970 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3970 = injectiveMoment H node2105 := by
  rfl

def raw3971 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

theorem canonical3971 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3971 = injectiveMoment H node626 := by
  rfl

def raw3972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]

def raw3972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]

def raw3972step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]

theorem canonical3972 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3972 = injectiveMoment H node2142 := by
  calc
    injectiveMoment H raw3972 = injectiveMoment H raw3972step0 := by
      have heq : raw3972step0 = -raw3972 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3972).symm
    injectiveMoment H raw3972step0 = injectiveMoment H raw3972step1 := by
      have heq : raw3972step1 = (fun i j => raw3972step0 (permutation180 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3972step0 permutation180 permutation8
    _ = injectiveMoment H node2142 := by rfl

def raw3973 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]

def raw3973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical3973 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3973 = injectiveMoment H node356 := by
  calc
    injectiveMoment H raw3973 = injectiveMoment H raw3973step0 := by
      have heq : raw3973step0 = (fun i j => raw3973 (permutation83 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3973 permutation83 permutation5
    _ = injectiveMoment H node356 := by rfl

def raw3974 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def raw3974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]

def raw3974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

theorem canonical3974 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3974 = injectiveMoment H node626 := by
  calc
    injectiveMoment H raw3974 = injectiveMoment H raw3974step0 := by
      have heq : raw3974step0 = -raw3974 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3974).symm
    injectiveMoment H raw3974step0 = injectiveMoment H raw3974step1 := by
      have heq : raw3974step1 = (fun i j => raw3974step0 (permutation41 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3974step0 permutation41 permutation8
    _ = injectiveMoment H node626 := by rfl

def raw3975 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def raw3975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical3975 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3975 = injectiveMoment H node704 := by
  calc
    injectiveMoment H raw3975 = injectiveMoment H raw3975step0 := by
      have heq : raw3975step0 = (fun i j => raw3975 (permutation83 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3975 permutation83 permutation5
    _ = injectiveMoment H node704 := by rfl

def raw3976 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]

def raw3976step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

theorem canonical3976 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3976 = injectiveMoment H node224 := by
  calc
    injectiveMoment H raw3976 = injectiveMoment H raw3976step0 := by
      have heq : raw3976step0 = (fun i j => raw3976 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3976 permutation22 permutation5
    _ = injectiveMoment H node224 := by rfl

def raw3977 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw3977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw3977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

theorem canonical3977 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3977 = injectiveMoment H node667 := by
  calc
    injectiveMoment H raw3977 = injectiveMoment H raw3977step0 := by
      have heq : raw3977step0 = -raw3977 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3977).symm
    injectiveMoment H raw3977step0 = injectiveMoment H raw3977step1 := by
      have heq : raw3977step1 = (fun i j => raw3977step0 (permutation41 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3977step0 permutation41 permutation8
    _ = injectiveMoment H node667 := by rfl

def raw3978 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]

def raw3978step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]

def raw3978step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical3978 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3978 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw3978 = injectiveMoment H raw3978step0 := by
      have heq : raw3978step0 = -raw3978 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3978).symm
    injectiveMoment H raw3978step0 = injectiveMoment H raw3978step1 := by
      have heq : raw3978step1 = (fun i j => raw3978step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3978step0 permutation11 permutation8
    _ = injectiveMoment H node210 := by rfl

def raw3979 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]

def raw3979step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical3979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3979 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw3979 = injectiveMoment H raw3979step0 := by
      have heq : raw3979step0 = (fun i j => raw3979 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3979 permutation28 permutation6
    _ = injectiveMoment H node111 := by rfl

def raw3980 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]

def raw3980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]

def raw3980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

theorem canonical3980 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3980 = injectiveMoment H node367 := by
  calc
    injectiveMoment H raw3980 = injectiveMoment H raw3980step0 := by
      have heq : raw3980step0 = -raw3980 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3980).symm
    injectiveMoment H raw3980step0 = injectiveMoment H raw3980step1 := by
      have heq : raw3980step1 = (fun i j => raw3980step0 (permutation69 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3980step0 permutation69 permutation5
    _ = injectiveMoment H node367 := by rfl

def raw3981 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical3981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3981 = injectiveMoment H node627 := by
  rfl

def raw3982 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def raw3982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]

theorem canonical3982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3982 = injectiveMoment H node354 := by
  calc
    injectiveMoment H raw3982 = injectiveMoment H raw3982step0 := by
      have heq : raw3982step0 = (fun i j => raw3982 (permutation83 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3982 permutation83 permutation5
    _ = injectiveMoment H node354 := by rfl

def raw3983 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![2, 0, -2]]

def raw3983step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

theorem canonical3983 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3983 = injectiveMoment H node101 := by
  calc
    injectiveMoment H raw3983 = injectiveMoment H raw3983step0 := by
      have heq : raw3983step0 = (fun i j => raw3983 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3983 permutation22 permutation5
    _ = injectiveMoment H node101 := by rfl

def raw3984 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def raw3984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]

def raw3984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

theorem canonical3984 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3984 = injectiveMoment H node368 := by
  calc
    injectiveMoment H raw3984 = injectiveMoment H raw3984step0 := by
      have heq : raw3984step0 = -raw3984 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3984).symm
    injectiveMoment H raw3984step0 = injectiveMoment H raw3984step1 := by
      have heq : raw3984step1 = (fun i j => raw3984step0 (permutation75 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3984step0 permutation75 permutation5
    _ = injectiveMoment H node368 := by rfl

def raw3985 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]

def raw3985step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![-1, 2, -1], ![-2, 1, 1]]

def raw3985step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

theorem canonical3985 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3985 = injectiveMoment H node111 := by
  calc
    injectiveMoment H raw3985 = injectiveMoment H raw3985step0 := by
      have heq : raw3985step0 = -raw3985 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3985).symm
    injectiveMoment H raw3985step0 = injectiveMoment H raw3985step1 := by
      have heq : raw3985step1 = (fun i j => raw3985step0 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3985step0 permutation16 permutation5
    _ = injectiveMoment H node111 := by rfl

def raw3986 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![2, -4, 2], ![1, 1, -2]]

def raw3986step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -3, 2], ![-2, 4, -2], ![-1, -1, 2]]

def raw3986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical3986 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3986 = injectiveMoment H node135 := by
  calc
    injectiveMoment H raw3986 = injectiveMoment H raw3986step0 := by
      have heq : raw3986step0 = -raw3986 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3986).symm
    injectiveMoment H raw3986step0 = injectiveMoment H raw3986step1 := by
      have heq : raw3986step1 = (fun i j => raw3986step0 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3986step0 permutation26 permutation4
    _ = injectiveMoment H node135 := by rfl

def raw3987 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -2, 2], ![1, -1, 0], ![2, -1, -1]]

theorem canonical3987 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3987 = injectiveMoment H node628 := by
  rfl

def raw3988 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -2, 2], ![2, -2, 0], ![1, 0, -1]]

def raw3988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -4, 3], ![0, 2, -2], ![-2, 2, 0], ![-1, 0, 1]]

def raw3988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]

theorem canonical3988 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3988 = injectiveMoment H node623 := by
  calc
    injectiveMoment H raw3988 = injectiveMoment H raw3988step0 := by
      have heq : raw3988step0 = -raw3988 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3988).symm
    injectiveMoment H raw3988step0 = injectiveMoment H raw3988step1 := by
      have heq : raw3988step1 = (fun i j => raw3988step0 (permutation127 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3988step0 permutation127 permutation4
    _ = injectiveMoment H node623 := by rfl

def raw3989 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -2, 2], ![3, -2, -1]]

def raw3989step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -4, 3], ![0, 2, -2], ![-3, 2, 1]]

def raw3989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]

theorem canonical3989 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3989 = injectiveMoment H node104 := by
  calc
    injectiveMoment H raw3989 = injectiveMoment H raw3989step0 := by
      have heq : raw3989step0 = -raw3989 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3989).symm
    injectiveMoment H raw3989step0 = injectiveMoment H raw3989step1 := by
      have heq : raw3989step1 = (fun i j => raw3989step0 (permutation32 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3989step0 permutation32 permutation4
    _ = injectiveMoment H node104 := by rfl

def raw3990 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical3990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3990 = injectiveMoment H node629 := by
  rfl

def raw3991 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

theorem canonical3991 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3991 = injectiveMoment H node191 := by
  rfl

def raw3992 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]

theorem canonical3992 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3992 = injectiveMoment H node630 := by
  rfl

def raw3993 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]

def raw3993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

theorem canonical3993 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3993 = injectiveMoment H node314 := by
  calc
    injectiveMoment H raw3993 = injectiveMoment H raw3993step0 := by
      have heq : raw3993step0 = (fun i j => raw3993 (permutation73 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3993 permutation73 permutation7
    _ = injectiveMoment H node314 := by rfl

def raw3994 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -2, 1], ![2, -2, 0]]

def raw3994step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical3994 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3994 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw3994 = injectiveMoment H raw3994step0 := by
      have heq : raw3994step0 = (fun i j => raw3994 (permutation20 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3994 permutation20 permutation7
    _ = injectiveMoment H node85 := by rfl

def raw3995 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![2, -4, 2], ![1, 0, -1]]

def raw3995step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -4, 3], ![-2, 4, -2], ![-1, 0, 1]]

def raw3995step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 3, -4], ![2, -2, 0]]

theorem canonical3995 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3995 = injectiveMoment H node133 := by
  calc
    injectiveMoment H raw3995 = injectiveMoment H raw3995step0 := by
      have heq : raw3995step0 = -raw3995 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3995).symm
    injectiveMoment H raw3995step0 = injectiveMoment H raw3995step1 := by
      have heq : raw3995step1 = (fun i j => raw3995step0 (permutation26 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3995step0 permutation26 permutation4
    _ = injectiveMoment H node133 := by rfl

def raw3996 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![2, -2, 0], ![1, -2, 1]]

def raw3996step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical3996 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3996 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw3996 = injectiveMoment H raw3996step0 := by
      have heq : raw3996step0 = (fun i j => raw3996 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3996 permutation18 permutation7
    _ = injectiveMoment H node85 := by rfl

def raw3997 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def raw3997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]

def raw3997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

theorem canonical3997 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3997 = injectiveMoment H node551 := by
  calc
    injectiveMoment H raw3997 = injectiveMoment H raw3997step0 := by
      have heq : raw3997step0 = -raw3997 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3997).symm
    injectiveMoment H raw3997step0 = injectiveMoment H raw3997step1 := by
      have heq : raw3997step1 = (fun i j => raw3997step0 (permutation144 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3997step0 permutation144 permutation3
    _ = injectiveMoment H node551 := by rfl

def raw3998 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical3998 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3998 = injectiveMoment H node631 := by
  rfl

def raw3999 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical3999 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3999 = injectiveMoment H node632 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
