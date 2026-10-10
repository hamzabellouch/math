import Mathlib.Tactic.FinCases
import OAI.Analysis.MutuallyUnbiased.PairMoments.PairCharges

namespace OAI

namespace MUB6

def pairPerm_0_1 : Equiv.Perm Coord where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_0_1_witness :
    (permuteCharge pairPerm_0_1.symm alpha = alpha ∨
      permuteCharge pairPerm_0_1.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_0_1.symm qCross = doubleDifference 0 1 ∨
      permuteCharge pairPerm_0_1.symm qSame = doubleDifference 0 1) := by
  constructor
  · left; decide +kernel
  · right; decide +kernel

def pairPerm_0_2 : Equiv.Perm Coord where
  toFun := ![0, 2, 1, 3, 4, 5]
  invFun := ![0, 2, 1, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_0_2_witness :
    (permuteCharge pairPerm_0_2.symm alpha = alpha ∨
      permuteCharge pairPerm_0_2.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_0_2.symm qCross = doubleDifference 0 2 ∨
      permuteCharge pairPerm_0_2.symm qSame = doubleDifference 0 2) := by
  constructor
  · left; decide +kernel
  · right; decide +kernel

def pairPerm_0_3 : Equiv.Perm Coord where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_0_3_witness :
    (permuteCharge pairPerm_0_3.symm alpha = alpha ∨
      permuteCharge pairPerm_0_3.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_0_3.symm qCross = doubleDifference 0 3 ∨
      permuteCharge pairPerm_0_3.symm qSame = doubleDifference 0 3) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

def pairPerm_0_4 : Equiv.Perm Coord where
  toFun := ![0, 1, 2, 4, 3, 5]
  invFun := ![0, 1, 2, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_0_4_witness :
    (permuteCharge pairPerm_0_4.symm alpha = alpha ∨
      permuteCharge pairPerm_0_4.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_0_4.symm qCross = doubleDifference 0 4 ∨
      permuteCharge pairPerm_0_4.symm qSame = doubleDifference 0 4) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

def pairPerm_0_5 : Equiv.Perm Coord where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_0_5_witness :
    (permuteCharge pairPerm_0_5.symm alpha = alpha ∨
      permuteCharge pairPerm_0_5.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_0_5.symm qCross = doubleDifference 0 5 ∨
      permuteCharge pairPerm_0_5.symm qSame = doubleDifference 0 5) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

def pairPerm_1_0 : Equiv.Perm Coord where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_1_0_witness :
    (permuteCharge pairPerm_1_0.symm alpha = alpha ∨
      permuteCharge pairPerm_1_0.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_1_0.symm qCross = doubleDifference 1 0 ∨
      permuteCharge pairPerm_1_0.symm qSame = doubleDifference 1 0) := by
  constructor
  · left; decide +kernel
  · right; decide +kernel

def pairPerm_1_2 : Equiv.Perm Coord where
  toFun := ![1, 2, 0, 3, 4, 5]
  invFun := ![2, 0, 1, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_1_2_witness :
    (permuteCharge pairPerm_1_2.symm alpha = alpha ∨
      permuteCharge pairPerm_1_2.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_1_2.symm qCross = doubleDifference 1 2 ∨
      permuteCharge pairPerm_1_2.symm qSame = doubleDifference 1 2) := by
  constructor
  · left; decide +kernel
  · right; decide +kernel

def pairPerm_1_3 : Equiv.Perm Coord where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_1_3_witness :
    (permuteCharge pairPerm_1_3.symm alpha = alpha ∨
      permuteCharge pairPerm_1_3.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_1_3.symm qCross = doubleDifference 1 3 ∨
      permuteCharge pairPerm_1_3.symm qSame = doubleDifference 1 3) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

def pairPerm_1_4 : Equiv.Perm Coord where
  toFun := ![1, 0, 2, 4, 3, 5]
  invFun := ![1, 0, 2, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_1_4_witness :
    (permuteCharge pairPerm_1_4.symm alpha = alpha ∨
      permuteCharge pairPerm_1_4.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_1_4.symm qCross = doubleDifference 1 4 ∨
      permuteCharge pairPerm_1_4.symm qSame = doubleDifference 1 4) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

def pairPerm_1_5 : Equiv.Perm Coord where
  toFun := ![1, 0, 2, 5, 3, 4]
  invFun := ![1, 0, 2, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_1_5_witness :
    (permuteCharge pairPerm_1_5.symm alpha = alpha ∨
      permuteCharge pairPerm_1_5.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_1_5.symm qCross = doubleDifference 1 5 ∨
      permuteCharge pairPerm_1_5.symm qSame = doubleDifference 1 5) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

def pairPerm_2_0 : Equiv.Perm Coord where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_2_0_witness :
    (permuteCharge pairPerm_2_0.symm alpha = alpha ∨
      permuteCharge pairPerm_2_0.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_2_0.symm qCross = doubleDifference 2 0 ∨
      permuteCharge pairPerm_2_0.symm qSame = doubleDifference 2 0) := by
  constructor
  · left; decide +kernel
  · right; decide +kernel

def pairPerm_2_1 : Equiv.Perm Coord where
  toFun := ![2, 1, 0, 3, 4, 5]
  invFun := ![2, 1, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_2_1_witness :
    (permuteCharge pairPerm_2_1.symm alpha = alpha ∨
      permuteCharge pairPerm_2_1.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_2_1.symm qCross = doubleDifference 2 1 ∨
      permuteCharge pairPerm_2_1.symm qSame = doubleDifference 2 1) := by
  constructor
  · left; decide +kernel
  · right; decide +kernel

def pairPerm_2_3 : Equiv.Perm Coord where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_2_3_witness :
    (permuteCharge pairPerm_2_3.symm alpha = alpha ∨
      permuteCharge pairPerm_2_3.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_2_3.symm qCross = doubleDifference 2 3 ∨
      permuteCharge pairPerm_2_3.symm qSame = doubleDifference 2 3) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

def pairPerm_2_4 : Equiv.Perm Coord where
  toFun := ![2, 0, 1, 4, 3, 5]
  invFun := ![1, 2, 0, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_2_4_witness :
    (permuteCharge pairPerm_2_4.symm alpha = alpha ∨
      permuteCharge pairPerm_2_4.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_2_4.symm qCross = doubleDifference 2 4 ∨
      permuteCharge pairPerm_2_4.symm qSame = doubleDifference 2 4) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

def pairPerm_2_5 : Equiv.Perm Coord where
  toFun := ![2, 0, 1, 5, 3, 4]
  invFun := ![1, 2, 0, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_2_5_witness :
    (permuteCharge pairPerm_2_5.symm alpha = alpha ∨
      permuteCharge pairPerm_2_5.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_2_5.symm qCross = doubleDifference 2 5 ∨
      permuteCharge pairPerm_2_5.symm qSame = doubleDifference 2 5) := by
  constructor
  · left; decide +kernel
  · left; decide +kernel

def pairPerm_3_0 : Equiv.Perm Coord where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_3_0_witness :
    (permuteCharge pairPerm_3_0.symm alpha = alpha ∨
      permuteCharge pairPerm_3_0.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_3_0.symm qCross = doubleDifference 3 0 ∨
      permuteCharge pairPerm_3_0.symm qSame = doubleDifference 3 0) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

def pairPerm_3_1 : Equiv.Perm Coord where
  toFun := ![3, 4, 5, 1, 0, 2]
  invFun := ![4, 3, 5, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_3_1_witness :
    (permuteCharge pairPerm_3_1.symm alpha = alpha ∨
      permuteCharge pairPerm_3_1.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_3_1.symm qCross = doubleDifference 3 1 ∨
      permuteCharge pairPerm_3_1.symm qSame = doubleDifference 3 1) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

def pairPerm_3_2 : Equiv.Perm Coord where
  toFun := ![3, 4, 5, 2, 0, 1]
  invFun := ![4, 5, 3, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_3_2_witness :
    (permuteCharge pairPerm_3_2.symm alpha = alpha ∨
      permuteCharge pairPerm_3_2.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_3_2.symm qCross = doubleDifference 3 2 ∨
      permuteCharge pairPerm_3_2.symm qSame = doubleDifference 3 2) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

def pairPerm_3_4 : Equiv.Perm Coord where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_3_4_witness :
    (permuteCharge pairPerm_3_4.symm alpha = alpha ∨
      permuteCharge pairPerm_3_4.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_3_4.symm qCross = doubleDifference 3 4 ∨
      permuteCharge pairPerm_3_4.symm qSame = doubleDifference 3 4) := by
  constructor
  · right; decide +kernel
  · right; decide +kernel

def pairPerm_3_5 : Equiv.Perm Coord where
  toFun := ![3, 5, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_3_5_witness :
    (permuteCharge pairPerm_3_5.symm alpha = alpha ∨
      permuteCharge pairPerm_3_5.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_3_5.symm qCross = doubleDifference 3 5 ∨
      permuteCharge pairPerm_3_5.symm qSame = doubleDifference 3 5) := by
  constructor
  · right; decide +kernel
  · right; decide +kernel

def pairPerm_4_0 : Equiv.Perm Coord where
  toFun := ![4, 3, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_4_0_witness :
    (permuteCharge pairPerm_4_0.symm alpha = alpha ∨
      permuteCharge pairPerm_4_0.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_4_0.symm qCross = doubleDifference 4 0 ∨
      permuteCharge pairPerm_4_0.symm qSame = doubleDifference 4 0) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

def pairPerm_4_1 : Equiv.Perm Coord where
  toFun := ![4, 3, 5, 1, 0, 2]
  invFun := ![4, 3, 5, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_4_1_witness :
    (permuteCharge pairPerm_4_1.symm alpha = alpha ∨
      permuteCharge pairPerm_4_1.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_4_1.symm qCross = doubleDifference 4 1 ∨
      permuteCharge pairPerm_4_1.symm qSame = doubleDifference 4 1) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

def pairPerm_4_2 : Equiv.Perm Coord where
  toFun := ![4, 3, 5, 2, 0, 1]
  invFun := ![4, 5, 3, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_4_2_witness :
    (permuteCharge pairPerm_4_2.symm alpha = alpha ∨
      permuteCharge pairPerm_4_2.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_4_2.symm qCross = doubleDifference 4 2 ∨
      permuteCharge pairPerm_4_2.symm qSame = doubleDifference 4 2) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

def pairPerm_4_3 : Equiv.Perm Coord where
  toFun := ![4, 3, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_4_3_witness :
    (permuteCharge pairPerm_4_3.symm alpha = alpha ∨
      permuteCharge pairPerm_4_3.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_4_3.symm qCross = doubleDifference 4 3 ∨
      permuteCharge pairPerm_4_3.symm qSame = doubleDifference 4 3) := by
  constructor
  · right; decide +kernel
  · right; decide +kernel

def pairPerm_4_5 : Equiv.Perm Coord where
  toFun := ![4, 5, 3, 0, 1, 2]
  invFun := ![3, 4, 5, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_4_5_witness :
    (permuteCharge pairPerm_4_5.symm alpha = alpha ∨
      permuteCharge pairPerm_4_5.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_4_5.symm qCross = doubleDifference 4 5 ∨
      permuteCharge pairPerm_4_5.symm qSame = doubleDifference 4 5) := by
  constructor
  · right; decide +kernel
  · right; decide +kernel

def pairPerm_5_0 : Equiv.Perm Coord where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_5_0_witness :
    (permuteCharge pairPerm_5_0.symm alpha = alpha ∨
      permuteCharge pairPerm_5_0.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_5_0.symm qCross = doubleDifference 5 0 ∨
      permuteCharge pairPerm_5_0.symm qSame = doubleDifference 5 0) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

def pairPerm_5_1 : Equiv.Perm Coord where
  toFun := ![5, 3, 4, 1, 0, 2]
  invFun := ![4, 3, 5, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_5_1_witness :
    (permuteCharge pairPerm_5_1.symm alpha = alpha ∨
      permuteCharge pairPerm_5_1.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_5_1.symm qCross = doubleDifference 5 1 ∨
      permuteCharge pairPerm_5_1.symm qSame = doubleDifference 5 1) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

def pairPerm_5_2 : Equiv.Perm Coord where
  toFun := ![5, 3, 4, 2, 0, 1]
  invFun := ![4, 5, 3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_5_2_witness :
    (permuteCharge pairPerm_5_2.symm alpha = alpha ∨
      permuteCharge pairPerm_5_2.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_5_2.symm qCross = doubleDifference 5 2 ∨
      permuteCharge pairPerm_5_2.symm qSame = doubleDifference 5 2) := by
  constructor
  · right; decide +kernel
  · left; decide +kernel

def pairPerm_5_3 : Equiv.Perm Coord where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_5_3_witness :
    (permuteCharge pairPerm_5_3.symm alpha = alpha ∨
      permuteCharge pairPerm_5_3.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_5_3.symm qCross = doubleDifference 5 3 ∨
      permuteCharge pairPerm_5_3.symm qSame = doubleDifference 5 3) := by
  constructor
  · right; decide +kernel
  · right; decide +kernel

def pairPerm_5_4 : Equiv.Perm Coord where
  toFun := ![5, 4, 3, 0, 1, 2]
  invFun := ![3, 4, 5, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem pairPerm_5_4_witness :
    (permuteCharge pairPerm_5_4.symm alpha = alpha ∨
      permuteCharge pairPerm_5_4.symm alpha = -alpha) ∧
    (permuteCharge pairPerm_5_4.symm qCross = doubleDifference 5 4 ∨
      permuteCharge pairPerm_5_4.symm qSame = doubleDifference 5 4) := by
  constructor
  · right; decide +kernel
  · right; decide +kernel

theorem pair_permutation_witness (i j : Coord) (hij : i ≠ j) :
    ∃ π : Equiv.Perm Coord,
      (permuteCharge π.symm alpha = alpha ∨ permuteCharge π.symm alpha = -alpha) ∧
      (permuteCharge π.symm qCross = doubleDifference i j ∨
        permuteCharge π.symm qSame = doubleDifference i j) := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact ⟨pairPerm_0_1, pairPerm_0_1_witness⟩
  · exact ⟨pairPerm_0_2, pairPerm_0_2_witness⟩
  · exact ⟨pairPerm_0_3, pairPerm_0_3_witness⟩
  · exact ⟨pairPerm_0_4, pairPerm_0_4_witness⟩
  · exact ⟨pairPerm_0_5, pairPerm_0_5_witness⟩
  · exact ⟨pairPerm_1_0, pairPerm_1_0_witness⟩
  · exact False.elim (hij rfl)
  · exact ⟨pairPerm_1_2, pairPerm_1_2_witness⟩
  · exact ⟨pairPerm_1_3, pairPerm_1_3_witness⟩
  · exact ⟨pairPerm_1_4, pairPerm_1_4_witness⟩
  · exact ⟨pairPerm_1_5, pairPerm_1_5_witness⟩
  · exact ⟨pairPerm_2_0, pairPerm_2_0_witness⟩
  · exact ⟨pairPerm_2_1, pairPerm_2_1_witness⟩
  · exact False.elim (hij rfl)
  · exact ⟨pairPerm_2_3, pairPerm_2_3_witness⟩
  · exact ⟨pairPerm_2_4, pairPerm_2_4_witness⟩
  · exact ⟨pairPerm_2_5, pairPerm_2_5_witness⟩
  · exact ⟨pairPerm_3_0, pairPerm_3_0_witness⟩
  · exact ⟨pairPerm_3_1, pairPerm_3_1_witness⟩
  · exact ⟨pairPerm_3_2, pairPerm_3_2_witness⟩
  · exact False.elim (hij rfl)
  · exact ⟨pairPerm_3_4, pairPerm_3_4_witness⟩
  · exact ⟨pairPerm_3_5, pairPerm_3_5_witness⟩
  · exact ⟨pairPerm_4_0, pairPerm_4_0_witness⟩
  · exact ⟨pairPerm_4_1, pairPerm_4_1_witness⟩
  · exact ⟨pairPerm_4_2, pairPerm_4_2_witness⟩
  · exact ⟨pairPerm_4_3, pairPerm_4_3_witness⟩
  · exact False.elim (hij rfl)
  · exact ⟨pairPerm_4_5, pairPerm_4_5_witness⟩
  · exact ⟨pairPerm_5_0, pairPerm_5_0_witness⟩
  · exact ⟨pairPerm_5_1, pairPerm_5_1_witness⟩
  · exact ⟨pairPerm_5_2, pairPerm_5_2_witness⟩
  · exact ⟨pairPerm_5_3, pairPerm_5_3_witness⟩
  · exact ⟨pairPerm_5_4, pairPerm_5_4_witness⟩
  · exact False.elim (hij rfl)

end MUB6

end OAI
