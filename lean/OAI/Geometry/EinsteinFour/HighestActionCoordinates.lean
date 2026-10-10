import OAI.Geometry.EinsteinFour.HighestVectorSpace

namespace OAI

/-! Exact coordinate action of the three total plus rotations. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- Simultaneous plus rotation of both derivative slots and the matrix slots. -/
def totalPlus (s : Fin 3) (X : Hessian) : Hessian := fun i j a b =>
  matrixAction s (X i j) a b +
    (∑ k, quaternionMatrix s i k * X k j a b) +
    ∑ k, quaternionMatrix s j k * X i k a b

/-- The same action in the twenty-one actual free coordinates. -/
def plusCoordinates (s : Fin 3) (c : Fin 21 → ℝ) : Fin 21 → ℝ :=
  ![
    ![-6 * c 1 - 2 * c 12 - 2 * c 20,
      6 * c 0 + 4 * c 7 + 6 * c 15 - 2 * c 16 - 2 * c 17,
      -5 * c 3 - c 4 + c 13,
      5 * c 2 - c 5 - 3 * c 8 - 2 * c 14,
      c 2 - 5 * c 5 + c 18,
      c 3 + 5 * c 4 - 3 * c 13 - 2 * c 19,
      -2 * c 11,
      -4 * c 10 - 2 * c 12,
      -2 * c 9 - 2 * c 13,
      2 * c 8 - 2 * c 14,
      2 * c 6 + 4 * c 7 - 2 * c 15,
      c 6 - c 16,
      c 7 - 4 * c 15 - c 17,
      c 8 - 2 * c 14 - c 18,
      c 9 + 2 * c 13 - c 19,
      c 10 + 2 * c 11 + 4 * c 12 - c 20,
      2 * c 11,
      2 * c 12 - 4 * c 20,
      2 * c 13 - 2 * c 19,
      2 * c 14 + 2 * c 18,
      2 * c 15 + 2 * c 16 + 4 * c 17],
    ![2 * c 4,
      2 * c 2 + 4 * c 5,
      -c 1 - c 20,
      c 0 + 3 * c 7 + 4 * c 15,
      -c 0 + c 17,
      -c 1 + 2 * c 12 + 3 * c 20,
      6 * c 9 - 2 * c 13,
      -2 * c 3 + 2 * c 13,
      4 * c 10 - 2 * c 12,
      -6 * c 6 - 4 * c 7 - 2 * c 15,
      2 * c 2 - 4 * c 8,
      c 8 + 6 * c 14 - c 18,
      -c 2 - c 5 + c 18,
      c 7 + 4 * c 15 - c 17,
      c 10 - 6 * c 11 - 4 * c 12 - c 20,
      -c 3 + c 4 - 3 * c 13,
      2 * c 13 + 6 * c 19,
      -2 * c 4,
      2 * c 12 + 4 * c 20,
      2 * c 15 - 6 * c 16 - 4 * c 17,
      -2 * c 5 - 2 * c 18],
    ![-6 * c 2 - 4 * c 5,
      -4 * c 3 + 2 * c 4 - 2 * c 13 - 2 * c 19,
      c 0 - 5 * c 7 - 4 * c 15,
      c 1 - 3 * c 10 + 2 * c 11 + 2 * c 12,
      -c 1 - 6 * c 12 - 5 * c 20,
      c 0 + c 7 - 2 * c 15 + 2 * c 16 + 2 * c 17,
      -6 * c 8 - 2 * c 14,
      2 * c 2 + 4 * c 8,
      2 * c 6 - 4 * c 7 - 2 * c 15,
      -4 * c 10 + 2 * c 11 + 2 * c 12,
      2 * c 3 + 2 * c 9,
      c 9 - 6 * c 13 - c 19,
      -c 3 + c 4 + 5 * c 13,
      c 10 + 2 * c 11 - 4 * c 12 - c 20,
      -c 6 - c 7 - 4 * c 15 + c 16 + c 17,
      c 2 + c 5 - c 8 + 2 * c 14,
      2 * c 14 - 6 * c 18,
      -2 * c 5 + 6 * c 18,
      2 * c 15 + 2 * c 16 - 4 * c 17,
      -2 * c 11 - 2 * c 12 - 4 * c 20,
      2 * c 4 - 2 * c 13 + 2 * c 19]
  ] s

@[simp] theorem plusCoordinates_0_0 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 0 = -6 * c 1 - 2 * c 12 - 2 * c 20 := rfl

@[simp] theorem plusCoordinates_0_1 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 1 = 6 * c 0 + 4 * c 7 + 6 * c 15 - 2 * c 16 - 2 * c 17 := rfl

@[simp] theorem plusCoordinates_0_2 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 2 = -5 * c 3 - c 4 + c 13 := rfl

@[simp] theorem plusCoordinates_0_3 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 3 = 5 * c 2 - c 5 - 3 * c 8 - 2 * c 14 := rfl

@[simp] theorem plusCoordinates_0_4 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 4 = c 2 - 5 * c 5 + c 18 := rfl

@[simp] theorem plusCoordinates_0_5 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 5 = c 3 + 5 * c 4 - 3 * c 13 - 2 * c 19 := rfl

@[simp] theorem plusCoordinates_0_6 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 6 = -2 * c 11 := rfl

@[simp] theorem plusCoordinates_0_7 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 7 = -4 * c 10 - 2 * c 12 := rfl

@[simp] theorem plusCoordinates_0_8 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 8 = -2 * c 9 - 2 * c 13 := rfl

@[simp] theorem plusCoordinates_0_9 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 9 = 2 * c 8 - 2 * c 14 := rfl

@[simp] theorem plusCoordinates_0_10 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 10 = 2 * c 6 + 4 * c 7 - 2 * c 15 := rfl

@[simp] theorem plusCoordinates_0_11 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 11 = c 6 - c 16 := rfl

@[simp] theorem plusCoordinates_0_12 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 12 = c 7 - 4 * c 15 - c 17 := rfl

@[simp] theorem plusCoordinates_0_13 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 13 = c 8 - 2 * c 14 - c 18 := rfl

@[simp] theorem plusCoordinates_0_14 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 14 = c 9 + 2 * c 13 - c 19 := rfl

@[simp] theorem plusCoordinates_0_15 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 15 = c 10 + 2 * c 11 + 4 * c 12 - c 20 := rfl

@[simp] theorem plusCoordinates_0_16 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 16 = 2 * c 11 := rfl

@[simp] theorem plusCoordinates_0_17 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 17 = 2 * c 12 - 4 * c 20 := rfl

@[simp] theorem plusCoordinates_0_18 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 18 = 2 * c 13 - 2 * c 19 := rfl

@[simp] theorem plusCoordinates_0_19 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 19 = 2 * c 14 + 2 * c 18 := rfl

@[simp] theorem plusCoordinates_0_20 (c : Fin 21 → ℝ) :
    plusCoordinates 0 c 20 = 2 * c 15 + 2 * c 16 + 4 * c 17 := rfl

@[simp] theorem plusCoordinates_1_0 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 0 = 2 * c 4 := rfl

@[simp] theorem plusCoordinates_1_1 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 1 = 2 * c 2 + 4 * c 5 := rfl

@[simp] theorem plusCoordinates_1_2 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 2 = -c 1 - c 20 := rfl

@[simp] theorem plusCoordinates_1_3 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 3 = c 0 + 3 * c 7 + 4 * c 15 := rfl

@[simp] theorem plusCoordinates_1_4 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 4 = -c 0 + c 17 := rfl

@[simp] theorem plusCoordinates_1_5 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 5 = -c 1 + 2 * c 12 + 3 * c 20 := rfl

@[simp] theorem plusCoordinates_1_6 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 6 = 6 * c 9 - 2 * c 13 := rfl

@[simp] theorem plusCoordinates_1_7 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 7 = -2 * c 3 + 2 * c 13 := rfl

@[simp] theorem plusCoordinates_1_8 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 8 = 4 * c 10 - 2 * c 12 := rfl

@[simp] theorem plusCoordinates_1_9 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 9 = -6 * c 6 - 4 * c 7 - 2 * c 15 := rfl

@[simp] theorem plusCoordinates_1_10 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 10 = 2 * c 2 - 4 * c 8 := rfl

@[simp] theorem plusCoordinates_1_11 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 11 = c 8 + 6 * c 14 - c 18 := rfl

@[simp] theorem plusCoordinates_1_12 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 12 = -c 2 - c 5 + c 18 := rfl

@[simp] theorem plusCoordinates_1_13 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 13 = c 7 + 4 * c 15 - c 17 := rfl

@[simp] theorem plusCoordinates_1_14 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 14 = c 10 - 6 * c 11 - 4 * c 12 - c 20 := rfl

@[simp] theorem plusCoordinates_1_15 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 15 = -c 3 + c 4 - 3 * c 13 := rfl

@[simp] theorem plusCoordinates_1_16 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 16 = 2 * c 13 + 6 * c 19 := rfl

@[simp] theorem plusCoordinates_1_17 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 17 = -2 * c 4 := rfl

@[simp] theorem plusCoordinates_1_18 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 18 = 2 * c 12 + 4 * c 20 := rfl

@[simp] theorem plusCoordinates_1_19 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 19 = 2 * c 15 - 6 * c 16 - 4 * c 17 := rfl

@[simp] theorem plusCoordinates_1_20 (c : Fin 21 → ℝ) :
    plusCoordinates 1 c 20 = -2 * c 5 - 2 * c 18 := rfl

@[simp] theorem plusCoordinates_2_0 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 0 = -6 * c 2 - 4 * c 5 := rfl

@[simp] theorem plusCoordinates_2_1 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 1 = -4 * c 3 + 2 * c 4 - 2 * c 13 - 2 * c 19 := rfl

@[simp] theorem plusCoordinates_2_2 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 2 = c 0 - 5 * c 7 - 4 * c 15 := rfl

@[simp] theorem plusCoordinates_2_3 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 3 = c 1 - 3 * c 10 + 2 * c 11 + 2 * c 12 := rfl

@[simp] theorem plusCoordinates_2_4 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 4 = -c 1 - 6 * c 12 - 5 * c 20 := rfl

@[simp] theorem plusCoordinates_2_5 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 5 = c 0 + c 7 - 2 * c 15 + 2 * c 16 + 2 * c 17 := rfl

@[simp] theorem plusCoordinates_2_6 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 6 = -6 * c 8 - 2 * c 14 := rfl

@[simp] theorem plusCoordinates_2_7 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 7 = 2 * c 2 + 4 * c 8 := rfl

@[simp] theorem plusCoordinates_2_8 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 8 = 2 * c 6 - 4 * c 7 - 2 * c 15 := rfl

@[simp] theorem plusCoordinates_2_9 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 9 = -4 * c 10 + 2 * c 11 + 2 * c 12 := rfl

@[simp] theorem plusCoordinates_2_10 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 10 = 2 * c 3 + 2 * c 9 := rfl

@[simp] theorem plusCoordinates_2_11 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 11 = c 9 - 6 * c 13 - c 19 := rfl

@[simp] theorem plusCoordinates_2_12 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 12 = -c 3 + c 4 + 5 * c 13 := rfl

@[simp] theorem plusCoordinates_2_13 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 13 = c 10 + 2 * c 11 - 4 * c 12 - c 20 := rfl

@[simp] theorem plusCoordinates_2_14 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 14 = -c 6 - c 7 - 4 * c 15 + c 16 + c 17 := rfl

@[simp] theorem plusCoordinates_2_15 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 15 = c 2 + c 5 - c 8 + 2 * c 14 := rfl

@[simp] theorem plusCoordinates_2_16 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 16 = 2 * c 14 - 6 * c 18 := rfl

@[simp] theorem plusCoordinates_2_17 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 17 = -2 * c 5 + 6 * c 18 := rfl

@[simp] theorem plusCoordinates_2_18 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 18 = 2 * c 15 + 2 * c 16 - 4 * c 17 := rfl

@[simp] theorem plusCoordinates_2_19 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 19 = -2 * c 11 - 2 * c 12 - 4 * c 20 := rfl

@[simp] theorem plusCoordinates_2_20 (c : Fin 21 → ℝ) :
    plusCoordinates 2 c 20 = 2 * c 4 - 2 * c 13 + 2 * c 19 := rfl

private theorem totalPlus_entry_0_0_0 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 0 0 = highest (plusCoordinates 0 c) 0 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_0_1 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 0 1 = highest (plusCoordinates 0 c) 0 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_0_2 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 0 2 = highest (plusCoordinates 0 c) 0 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_0_3 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 0 3 = highest (plusCoordinates 0 c) 0 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_1_0 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 1 0 = highest (plusCoordinates 0 c) 1 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_1_1 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 1 1 = highest (plusCoordinates 0 c) 1 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_1_2 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 1 2 = highest (plusCoordinates 0 c) 1 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_1_3 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 1 3 = highest (plusCoordinates 0 c) 1 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_2_0 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 2 0 = highest (plusCoordinates 0 c) 2 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_2_1 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 2 1 = highest (plusCoordinates 0 c) 2 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_2_2 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 2 2 = highest (plusCoordinates 0 c) 2 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_2_3 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 2 3 = highest (plusCoordinates 0 c) 2 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_3_0 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 3 0 = highest (plusCoordinates 0 c) 3 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_3_1 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 3 1 = highest (plusCoordinates 0 c) 3 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_3_2 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 3 2 = highest (plusCoordinates 0 c) 3 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_0_3_3 (c : Fin 21 → ℝ) :
    totalPlus 0 (highest c) 3 3 = highest (plusCoordinates 0 c) 3 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_0_0 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 0 0 = highest (plusCoordinates 1 c) 0 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_0_1 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 0 1 = highest (plusCoordinates 1 c) 0 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_0_2 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 0 2 = highest (plusCoordinates 1 c) 0 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_0_3 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 0 3 = highest (plusCoordinates 1 c) 0 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_1_0 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 1 0 = highest (plusCoordinates 1 c) 1 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_1_1 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 1 1 = highest (plusCoordinates 1 c) 1 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_1_2 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 1 2 = highest (plusCoordinates 1 c) 1 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_1_3 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 1 3 = highest (plusCoordinates 1 c) 1 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_2_0 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 2 0 = highest (plusCoordinates 1 c) 2 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_2_1 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 2 1 = highest (plusCoordinates 1 c) 2 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_2_2 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 2 2 = highest (plusCoordinates 1 c) 2 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_2_3 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 2 3 = highest (plusCoordinates 1 c) 2 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_3_0 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 3 0 = highest (plusCoordinates 1 c) 3 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_3_1 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 3 1 = highest (plusCoordinates 1 c) 3 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates] <;> ring)

private theorem totalPlus_entry_1_3_2 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 3 2 = highest (plusCoordinates 1 c) 3 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_1_3_3 (c : Fin 21 → ℝ) :
    totalPlus 1 (highest c) 3 3 = highest (plusCoordinates 1 c) 3 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_0_0 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 0 0 = highest (plusCoordinates 2 c) 0 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_0_1 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 0 1 = highest (plusCoordinates 2 c) 0 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_0_2 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 0 2 = highest (plusCoordinates 2 c) 0 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_0_3 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 0 3 = highest (plusCoordinates 2 c) 0 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_1_0 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 1 0 = highest (plusCoordinates 2 c) 1 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_1_1 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 1 1 = highest (plusCoordinates 2 c) 1 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_1_2 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 1 2 = highest (plusCoordinates 2 c) 1 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_1_3 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 1 3 = highest (plusCoordinates 2 c) 1 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_2_0 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 2 0 = highest (plusCoordinates 2 c) 2 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_2_1 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 2 1 = highest (plusCoordinates 2 c) 2 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_2_2 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 2 2 = highest (plusCoordinates 2 c) 2 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_2_3 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 2 3 = highest (plusCoordinates 2 c) 2 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_3_0 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 3 0 = highest (plusCoordinates 2 c) 3 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_3_1 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 3 1 = highest (plusCoordinates 2 c) 3 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_3_2 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 3 2 = highest (plusCoordinates 2 c) 3 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem totalPlus_entry_2_3_3 (c : Fin 21 → ℝ) :
    totalPlus 2 (highest c) 3 3 = highest (plusCoordinates 2 c) 3 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, quaternionMatrix, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

/-- The total plus rotation preserves the explicit constrained space. -/
theorem totalPlus_highest (s : Fin 3) (c : Fin 21 → ℝ) :
    totalPlus s (highest c) = highest (plusCoordinates s c) := by
  funext i j
  fin_cases s <;> fin_cases i <;> fin_cases j
  · exact totalPlus_entry_0_0_0 c
  · exact totalPlus_entry_0_0_1 c
  · exact totalPlus_entry_0_0_2 c
  · exact totalPlus_entry_0_0_3 c
  · exact totalPlus_entry_0_1_0 c
  · exact totalPlus_entry_0_1_1 c
  · exact totalPlus_entry_0_1_2 c
  · exact totalPlus_entry_0_1_3 c
  · exact totalPlus_entry_0_2_0 c
  · exact totalPlus_entry_0_2_1 c
  · exact totalPlus_entry_0_2_2 c
  · exact totalPlus_entry_0_2_3 c
  · exact totalPlus_entry_0_3_0 c
  · exact totalPlus_entry_0_3_1 c
  · exact totalPlus_entry_0_3_2 c
  · exact totalPlus_entry_0_3_3 c
  · exact totalPlus_entry_1_0_0 c
  · exact totalPlus_entry_1_0_1 c
  · exact totalPlus_entry_1_0_2 c
  · exact totalPlus_entry_1_0_3 c
  · exact totalPlus_entry_1_1_0 c
  · exact totalPlus_entry_1_1_1 c
  · exact totalPlus_entry_1_1_2 c
  · exact totalPlus_entry_1_1_3 c
  · exact totalPlus_entry_1_2_0 c
  · exact totalPlus_entry_1_2_1 c
  · exact totalPlus_entry_1_2_2 c
  · exact totalPlus_entry_1_2_3 c
  · exact totalPlus_entry_1_3_0 c
  · exact totalPlus_entry_1_3_1 c
  · exact totalPlus_entry_1_3_2 c
  · exact totalPlus_entry_1_3_3 c
  · exact totalPlus_entry_2_0_0 c
  · exact totalPlus_entry_2_0_1 c
  · exact totalPlus_entry_2_0_2 c
  · exact totalPlus_entry_2_0_3 c
  · exact totalPlus_entry_2_1_0 c
  · exact totalPlus_entry_2_1_1 c
  · exact totalPlus_entry_2_1_2 c
  · exact totalPlus_entry_2_1_3 c
  · exact totalPlus_entry_2_2_0 c
  · exact totalPlus_entry_2_2_1 c
  · exact totalPlus_entry_2_2_2 c
  · exact totalPlus_entry_2_2_3 c
  · exact totalPlus_entry_2_3_0 c
  · exact totalPlus_entry_2_3_1 c
  · exact totalPlus_entry_2_3_2 c
  · exact totalPlus_entry_2_3_3 c

private theorem coordinate_casimir_0 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 0 +
      plusCoordinates 1 (plusCoordinates 1 c) 0 +
      plusCoordinates 2 (plusCoordinates 2 c) 0 = -48 * c 0 := by
  simp; ring

private theorem coordinate_casimir_1 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 1 +
      plusCoordinates 1 (plusCoordinates 1 c) 1 +
      plusCoordinates 2 (plusCoordinates 2 c) 1 = -48 * c 1 := by
  simp; ring

private theorem coordinate_casimir_2 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 2 +
      plusCoordinates 1 (plusCoordinates 1 c) 2 +
      plusCoordinates 2 (plusCoordinates 2 c) 2 = -48 * c 2 := by
  simp; ring

private theorem coordinate_casimir_3 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 3 +
      plusCoordinates 1 (plusCoordinates 1 c) 3 +
      plusCoordinates 2 (plusCoordinates 2 c) 3 = -48 * c 3 := by
  simp; ring

private theorem coordinate_casimir_4 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 4 +
      plusCoordinates 1 (plusCoordinates 1 c) 4 +
      plusCoordinates 2 (plusCoordinates 2 c) 4 = -48 * c 4 := by
  simp; ring

private theorem coordinate_casimir_5 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 5 +
      plusCoordinates 1 (plusCoordinates 1 c) 5 +
      plusCoordinates 2 (plusCoordinates 2 c) 5 = -48 * c 5 := by
  simp; ring

private theorem coordinate_casimir_6 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 6 +
      plusCoordinates 1 (plusCoordinates 1 c) 6 +
      plusCoordinates 2 (plusCoordinates 2 c) 6 = -48 * c 6 := by
  simp; ring

private theorem coordinate_casimir_7 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 7 +
      plusCoordinates 1 (plusCoordinates 1 c) 7 +
      plusCoordinates 2 (plusCoordinates 2 c) 7 = -48 * c 7 := by
  simp; ring

private theorem coordinate_casimir_8 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 8 +
      plusCoordinates 1 (plusCoordinates 1 c) 8 +
      plusCoordinates 2 (plusCoordinates 2 c) 8 = -48 * c 8 := by
  simp; ring

private theorem coordinate_casimir_9 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 9 +
      plusCoordinates 1 (plusCoordinates 1 c) 9 +
      plusCoordinates 2 (plusCoordinates 2 c) 9 = -48 * c 9 := by
  simp; ring

private theorem coordinate_casimir_10 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 10 +
      plusCoordinates 1 (plusCoordinates 1 c) 10 +
      plusCoordinates 2 (plusCoordinates 2 c) 10 = -48 * c 10 := by
  simp; ring

private theorem coordinate_casimir_11 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 11 +
      plusCoordinates 1 (plusCoordinates 1 c) 11 +
      plusCoordinates 2 (plusCoordinates 2 c) 11 = -48 * c 11 := by
  simp; ring

private theorem coordinate_casimir_12 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 12 +
      plusCoordinates 1 (plusCoordinates 1 c) 12 +
      plusCoordinates 2 (plusCoordinates 2 c) 12 = -48 * c 12 := by
  simp; ring

private theorem coordinate_casimir_13 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 13 +
      plusCoordinates 1 (plusCoordinates 1 c) 13 +
      plusCoordinates 2 (plusCoordinates 2 c) 13 = -48 * c 13 := by
  simp; ring

private theorem coordinate_casimir_14 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 14 +
      plusCoordinates 1 (plusCoordinates 1 c) 14 +
      plusCoordinates 2 (plusCoordinates 2 c) 14 = -48 * c 14 := by
  simp; ring

private theorem coordinate_casimir_15 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 15 +
      plusCoordinates 1 (plusCoordinates 1 c) 15 +
      plusCoordinates 2 (plusCoordinates 2 c) 15 = -48 * c 15 := by
  simp; ring

private theorem coordinate_casimir_16 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 16 +
      plusCoordinates 1 (plusCoordinates 1 c) 16 +
      plusCoordinates 2 (plusCoordinates 2 c) 16 = -48 * c 16 := by
  simp; ring

private theorem coordinate_casimir_17 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 17 +
      plusCoordinates 1 (plusCoordinates 1 c) 17 +
      plusCoordinates 2 (plusCoordinates 2 c) 17 = -48 * c 17 := by
  simp; ring

private theorem coordinate_casimir_18 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 18 +
      plusCoordinates 1 (plusCoordinates 1 c) 18 +
      plusCoordinates 2 (plusCoordinates 2 c) 18 = -48 * c 18 := by
  simp; ring

private theorem coordinate_casimir_19 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 19 +
      plusCoordinates 1 (plusCoordinates 1 c) 19 +
      plusCoordinates 2 (plusCoordinates 2 c) 19 = -48 * c 19 := by
  simp; ring

private theorem coordinate_casimir_20 (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) 20 +
      plusCoordinates 1 (plusCoordinates 1 c) 20 +
      plusCoordinates 2 (plusCoordinates 2 c) 20 = -48 * c 20 := by
  simp; ring

/-- The spin-three Casimir is proved on the actual coordinate action. -/
theorem coordinate_casimir (c : Fin 21 → ℝ) :
    plusCoordinates 0 (plusCoordinates 0 c) +
      plusCoordinates 1 (plusCoordinates 1 c) +
      plusCoordinates 2 (plusCoordinates 2 c) = (-48 : ℝ) • c := by
  funext k
  fin_cases k
  · exact coordinate_casimir_0 c
  · exact coordinate_casimir_1 c
  · exact coordinate_casimir_2 c
  · exact coordinate_casimir_3 c
  · exact coordinate_casimir_4 c
  · exact coordinate_casimir_5 c
  · exact coordinate_casimir_6 c
  · exact coordinate_casimir_7 c
  · exact coordinate_casimir_8 c
  · exact coordinate_casimir_9 c
  · exact coordinate_casimir_10 c
  · exact coordinate_casimir_11 c
  · exact coordinate_casimir_12 c
  · exact coordinate_casimir_13 c
  · exact coordinate_casimir_14 c
  · exact coordinate_casimir_15 c
  · exact coordinate_casimir_16 c
  · exact coordinate_casimir_17 c
  · exact coordinate_casimir_18 c
  · exact coordinate_casimir_19 c
  · exact coordinate_casimir_20 c


end
end PositiveEinsteinFour.HighestHessian

end OAI
