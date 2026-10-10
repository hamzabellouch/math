import OAI.Geometry.EinsteinFour.HighestAction

namespace OAI

/-! Exact coordinate action of the three total minus rotations. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- Right quaternion multiplication, commuting with the fixed left frame. -/
def rightQuaternion (s : Fin 3) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![![0, -1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, -1, 0]],
    ![![0, 0, -1, 0], ![0, 0, 0, -1], ![1, 0, 0, 0], ![0, 1, 0, 0]],
    ![![0, 0, 0, -1], ![0, 0, 1, 0], ![0, -1, 0, 0], ![1, 0, 0, 0]]] s

def totalMinus (s : Fin 3) (X : Hessian) : Hessian := fun i j a b =>
  (∑ k, rightQuaternion s i k * X k j a b) +
    ∑ k, rightQuaternion s j k * X i k a b

def minusCoordinates (s : Fin 3) (c : Fin 21 → ℝ) : Fin 21 → ℝ :=
  ![
    ![-2 * c 1 - 2 * c 12 - 2 * c 20,
      2 * c 0 + 2 * c 7 + 2 * c 15,
      -c 3 + c 4 + c 13,
      c 2 + c 5 - c 8,
      -c 2 - c 5 + c 18,
      -c 3 + c 4 - c 13,
      2 * c 11,
      2 * c 12,
      2 * c 13,
      2 * c 14,
      2 * c 15,
      -c 6 + c 16,
      -c 7 + c 17,
      -c 8 + c 18,
      -c 9 + c 19,
      -c 10 + c 20,
      -2 * c 11,
      -2 * c 12,
      -2 * c 13,
      -2 * c 14,
      -2 * c 15],
    ![-2 * c 4,
      -2 * c 5,
      -c 1 - 2 * c 12 - c 20,
      c 0 + c 7,
      c 0 - c 17,
      c 1 - c 20,
      2 * c 9 - 2 * c 13,
      -2 * c 3 + 2 * c 13,
      2 * c 10 - 2 * c 12,
      -2 * c 6 - 2 * c 7 - 2 * c 15,
      2 * c 2 - 2 * c 8,
      -c 8 - c 18,
      c 2 - c 5 + c 18,
      -c 7 - c 17,
      -c 10 - c 20,
      c 3 + c 4 - c 13,
      -2 * c 13 - 2 * c 19,
      2 * c 4,
      -2 * c 12 - 2 * c 20,
      -2 * c 15 + 2 * c 16 + 2 * c 17,
      2 * c 5],
    ![2 * c 2,
      2 * c 3,
      -c 0 + c 7,
      -c 1 + c 10,
      -c 1 - c 20,
      c 0 + c 7 + 2 * c 15,
      2 * c 8 + 2 * c 14,
      -2 * c 2,
      2 * c 7 + 2 * c 15,
      2 * c 10 - 2 * c 11 - 2 * c 12,
      -2 * c 3,
      c 9 + c 19,
      -c 3 - c 4 + c 13,
      c 10 + c 20,
      -c 6 - c 7 - c 16 - c 17,
      c 2 - c 5 - c 8,
      2 * c 14 - 2 * c 18,
      -2 * c 5 + 2 * c 18,
      2 * c 15 - 2 * c 17,
      -2 * c 11 - 2 * c 12 - 2 * c 20,
      2 * c 4 - 2 * c 13]
  ] s

@[simp] theorem minusCoordinates_0_0 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 0 = -2 * c 1 - 2 * c 12 - 2 * c 20 := rfl

@[simp] theorem minusCoordinates_0_1 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 1 = 2 * c 0 + 2 * c 7 + 2 * c 15 := rfl

@[simp] theorem minusCoordinates_0_2 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 2 = -c 3 + c 4 + c 13 := rfl

@[simp] theorem minusCoordinates_0_3 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 3 = c 2 + c 5 - c 8 := rfl

@[simp] theorem minusCoordinates_0_4 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 4 = -c 2 - c 5 + c 18 := rfl

@[simp] theorem minusCoordinates_0_5 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 5 = -c 3 + c 4 - c 13 := rfl

@[simp] theorem minusCoordinates_0_6 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 6 = 2 * c 11 := rfl

@[simp] theorem minusCoordinates_0_7 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 7 = 2 * c 12 := rfl

@[simp] theorem minusCoordinates_0_8 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 8 = 2 * c 13 := rfl

@[simp] theorem minusCoordinates_0_9 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 9 = 2 * c 14 := rfl

@[simp] theorem minusCoordinates_0_10 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 10 = 2 * c 15 := rfl

@[simp] theorem minusCoordinates_0_11 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 11 = -c 6 + c 16 := rfl

@[simp] theorem minusCoordinates_0_12 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 12 = -c 7 + c 17 := rfl

@[simp] theorem minusCoordinates_0_13 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 13 = -c 8 + c 18 := rfl

@[simp] theorem minusCoordinates_0_14 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 14 = -c 9 + c 19 := rfl

@[simp] theorem minusCoordinates_0_15 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 15 = -c 10 + c 20 := rfl

@[simp] theorem minusCoordinates_0_16 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 16 = -2 * c 11 := rfl

@[simp] theorem minusCoordinates_0_17 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 17 = -2 * c 12 := rfl

@[simp] theorem minusCoordinates_0_18 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 18 = -2 * c 13 := rfl

@[simp] theorem minusCoordinates_0_19 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 19 = -2 * c 14 := rfl

@[simp] theorem minusCoordinates_0_20 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 20 = -2 * c 15 := rfl

@[simp] theorem minusCoordinates_1_0 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 0 = -2 * c 4 := rfl

@[simp] theorem minusCoordinates_1_1 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 1 = -2 * c 5 := rfl

@[simp] theorem minusCoordinates_1_2 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 2 = -c 1 - 2 * c 12 - c 20 := rfl

@[simp] theorem minusCoordinates_1_3 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 3 = c 0 + c 7 := rfl

@[simp] theorem minusCoordinates_1_4 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 4 = c 0 - c 17 := rfl

@[simp] theorem minusCoordinates_1_5 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 5 = c 1 - c 20 := rfl

@[simp] theorem minusCoordinates_1_6 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 6 = 2 * c 9 - 2 * c 13 := rfl

@[simp] theorem minusCoordinates_1_7 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 7 = -2 * c 3 + 2 * c 13 := rfl

@[simp] theorem minusCoordinates_1_8 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 8 = 2 * c 10 - 2 * c 12 := rfl

@[simp] theorem minusCoordinates_1_9 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 9 = -2 * c 6 - 2 * c 7 - 2 * c 15 := rfl

@[simp] theorem minusCoordinates_1_10 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 10 = 2 * c 2 - 2 * c 8 := rfl

@[simp] theorem minusCoordinates_1_11 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 11 = -c 8 - c 18 := rfl

@[simp] theorem minusCoordinates_1_12 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 12 = c 2 - c 5 + c 18 := rfl

@[simp] theorem minusCoordinates_1_13 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 13 = -c 7 - c 17 := rfl

@[simp] theorem minusCoordinates_1_14 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 14 = -c 10 - c 20 := rfl

@[simp] theorem minusCoordinates_1_15 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 15 = c 3 + c 4 - c 13 := rfl

@[simp] theorem minusCoordinates_1_16 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 16 = -2 * c 13 - 2 * c 19 := rfl

@[simp] theorem minusCoordinates_1_17 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 17 = 2 * c 4 := rfl

@[simp] theorem minusCoordinates_1_18 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 18 = -2 * c 12 - 2 * c 20 := rfl

@[simp] theorem minusCoordinates_1_19 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 19 = -2 * c 15 + 2 * c 16 + 2 * c 17 := rfl

@[simp] theorem minusCoordinates_1_20 (c : Fin 21 → ℝ) :
    minusCoordinates 1 c 20 = 2 * c 5 := rfl

@[simp] theorem minusCoordinates_2_0 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 0 = 2 * c 2 := rfl

@[simp] theorem minusCoordinates_2_1 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 1 = 2 * c 3 := rfl

@[simp] theorem minusCoordinates_2_2 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 2 = -c 0 + c 7 := rfl

@[simp] theorem minusCoordinates_2_3 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 3 = -c 1 + c 10 := rfl

@[simp] theorem minusCoordinates_2_4 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 4 = -c 1 - c 20 := rfl

@[simp] theorem minusCoordinates_2_5 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 5 = c 0 + c 7 + 2 * c 15 := rfl

@[simp] theorem minusCoordinates_2_6 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 6 = 2 * c 8 + 2 * c 14 := rfl

@[simp] theorem minusCoordinates_2_7 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 7 = -2 * c 2 := rfl

@[simp] theorem minusCoordinates_2_8 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 8 = 2 * c 7 + 2 * c 15 := rfl

@[simp] theorem minusCoordinates_2_9 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 9 = 2 * c 10 - 2 * c 11 - 2 * c 12 := rfl

@[simp] theorem minusCoordinates_2_10 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 10 = -2 * c 3 := rfl

@[simp] theorem minusCoordinates_2_11 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 11 = c 9 + c 19 := rfl

@[simp] theorem minusCoordinates_2_12 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 12 = -c 3 - c 4 + c 13 := rfl

@[simp] theorem minusCoordinates_2_13 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 13 = c 10 + c 20 := rfl

@[simp] theorem minusCoordinates_2_14 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 14 = -c 6 - c 7 - c 16 - c 17 := rfl

@[simp] theorem minusCoordinates_2_15 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 15 = c 2 - c 5 - c 8 := rfl

@[simp] theorem minusCoordinates_2_16 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 16 = 2 * c 14 - 2 * c 18 := rfl

@[simp] theorem minusCoordinates_2_17 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 17 = -2 * c 5 + 2 * c 18 := rfl

@[simp] theorem minusCoordinates_2_18 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 18 = 2 * c 15 - 2 * c 17 := rfl

@[simp] theorem minusCoordinates_2_19 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 19 = -2 * c 11 - 2 * c 12 - 2 * c 20 := rfl

@[simp] theorem minusCoordinates_2_20 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 20 = 2 * c 4 - 2 * c 13 := rfl

private theorem totalMinus_entry_0_0_0 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 0 0 = highest (minusCoordinates 0 c) 0 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_0_1 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 0 1 = highest (minusCoordinates 0 c) 0 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_0_2 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 0 2 = highest (minusCoordinates 0 c) 0 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_0_3 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 0 3 = highest (minusCoordinates 0 c) 0 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_1_0 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 1 0 = highest (minusCoordinates 0 c) 1 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_1_1 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 1 1 = highest (minusCoordinates 0 c) 1 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_1_2 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 1 2 = highest (minusCoordinates 0 c) 1 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_1_3 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 1 3 = highest (minusCoordinates 0 c) 1 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_2_0 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 2 0 = highest (minusCoordinates 0 c) 2 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_2_1 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 2 1 = highest (minusCoordinates 0 c) 2 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_2_2 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 2 2 = highest (minusCoordinates 0 c) 2 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_2_3 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 2 3 = highest (minusCoordinates 0 c) 2 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_3_0 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 3 0 = highest (minusCoordinates 0 c) 3 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_3_1 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 3 1 = highest (minusCoordinates 0 c) 3 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_0_3_2 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 3 2 = highest (minusCoordinates 0 c) 3 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ]
  all_goals ring

private theorem totalMinus_entry_0_3_3 (c : Fin 21 → ℝ) :
    totalMinus 0 (highest c) 3 3 = highest (minusCoordinates 0 c) 3 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_0_0 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 0 0 = highest (minusCoordinates 1 c) 0 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_0_1 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 0 1 = highest (minusCoordinates 1 c) 0 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_0_2 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 0 2 = highest (minusCoordinates 1 c) 0 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_0_3 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 0 3 = highest (minusCoordinates 1 c) 0 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_1_0 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 1 0 = highest (minusCoordinates 1 c) 1 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_1_1 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 1 1 = highest (minusCoordinates 1 c) 1 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_1_2 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 1 2 = highest (minusCoordinates 1 c) 1 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_1_3 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 1 3 = highest (minusCoordinates 1 c) 1 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_2_0 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 2 0 = highest (minusCoordinates 1 c) 2 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_2_1 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 2 1 = highest (minusCoordinates 1 c) 2 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_2_2 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 2 2 = highest (minusCoordinates 1 c) 2 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_2_3 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 2 3 = highest (minusCoordinates 1 c) 2 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_3_0 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 3 0 = highest (minusCoordinates 1 c) 3 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_3_1 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 3 1 = highest (minusCoordinates 1 c) 3 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_3_2 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 3 2 = highest (minusCoordinates 1 c) 3 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_1_3_3 (c : Fin 21 → ℝ) :
    totalMinus 1 (highest c) 3 3 = highest (minusCoordinates 1 c) 3 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_0_0 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 0 0 = highest (minusCoordinates 2 c) 0 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_0_1 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 0 1 = highest (minusCoordinates 2 c) 0 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_0_2 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 0 2 = highest (minusCoordinates 2 c) 0 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_0_3 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 0 3 = highest (minusCoordinates 2 c) 0 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_1_0 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 1 0 = highest (minusCoordinates 2 c) 1 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_1_1 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 1 1 = highest (minusCoordinates 2 c) 1 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_1_2 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 1 2 = highest (minusCoordinates 2 c) 1 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_1_3 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 1 3 = highest (minusCoordinates 2 c) 1 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_2_0 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 2 0 = highest (minusCoordinates 2 c) 2 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_2_1 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 2 1 = highest (minusCoordinates 2 c) 2 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_2_2 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 2 2 = highest (minusCoordinates 2 c) 2 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_2_3 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 2 3 = highest (minusCoordinates 2 c) 2 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_3_0 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 3 0 = highest (minusCoordinates 2 c) 3 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_3_1 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 3 1 = highest (minusCoordinates 2 c) 3 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_3_2 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 3 2 = highest (minusCoordinates 2 c) 3 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

private theorem totalMinus_entry_2_3_3 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 3 3 = highest (minusCoordinates 2 c) 3 3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMinus, rightQuaternion, ofCoordinates, Fin.sum_univ_succ] <;> ring

theorem totalMinus_highest (s : Fin 3) (c : Fin 21 → ℝ) :
    totalMinus s (highest c) = highest (minusCoordinates s c) := by
  funext i j
  fin_cases s <;> fin_cases i <;> fin_cases j
  · exact totalMinus_entry_0_0_0 c
  · exact totalMinus_entry_0_0_1 c
  · exact totalMinus_entry_0_0_2 c
  · exact totalMinus_entry_0_0_3 c
  · exact totalMinus_entry_0_1_0 c
  · exact totalMinus_entry_0_1_1 c
  · exact totalMinus_entry_0_1_2 c
  · exact totalMinus_entry_0_1_3 c
  · exact totalMinus_entry_0_2_0 c
  · exact totalMinus_entry_0_2_1 c
  · exact totalMinus_entry_0_2_2 c
  · exact totalMinus_entry_0_2_3 c
  · exact totalMinus_entry_0_3_0 c
  · exact totalMinus_entry_0_3_1 c
  · exact totalMinus_entry_0_3_2 c
  · exact totalMinus_entry_0_3_3 c
  · exact totalMinus_entry_1_0_0 c
  · exact totalMinus_entry_1_0_1 c
  · exact totalMinus_entry_1_0_2 c
  · exact totalMinus_entry_1_0_3 c
  · exact totalMinus_entry_1_1_0 c
  · exact totalMinus_entry_1_1_1 c
  · exact totalMinus_entry_1_1_2 c
  · exact totalMinus_entry_1_1_3 c
  · exact totalMinus_entry_1_2_0 c
  · exact totalMinus_entry_1_2_1 c
  · exact totalMinus_entry_1_2_2 c
  · exact totalMinus_entry_1_2_3 c
  · exact totalMinus_entry_1_3_0 c
  · exact totalMinus_entry_1_3_1 c
  · exact totalMinus_entry_1_3_2 c
  · exact totalMinus_entry_1_3_3 c
  · exact totalMinus_entry_2_0_0 c
  · exact totalMinus_entry_2_0_1 c
  · exact totalMinus_entry_2_0_2 c
  · exact totalMinus_entry_2_0_3 c
  · exact totalMinus_entry_2_1_0 c
  · exact totalMinus_entry_2_1_1 c
  · exact totalMinus_entry_2_1_2 c
  · exact totalMinus_entry_2_1_3 c
  · exact totalMinus_entry_2_2_0 c
  · exact totalMinus_entry_2_2_1 c
  · exact totalMinus_entry_2_2_2 c
  · exact totalMinus_entry_2_2_3 c
  · exact totalMinus_entry_2_3_0 c
  · exact totalMinus_entry_2_3_1 c
  · exact totalMinus_entry_2_3_2 c
  · exact totalMinus_entry_2_3_3 c

private theorem minus_coordinate_casimir_0 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 0 +
      minusCoordinates 1 (minusCoordinates 1 c) 0 +
      minusCoordinates 2 (minusCoordinates 2 c) 0 = -8 * c 0 := by
  simp; ring

private theorem minus_coordinate_casimir_1 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 1 +
      minusCoordinates 1 (minusCoordinates 1 c) 1 +
      minusCoordinates 2 (minusCoordinates 2 c) 1 = -8 * c 1 := by
  simp; ring

private theorem minus_coordinate_casimir_2 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 2 +
      minusCoordinates 1 (minusCoordinates 1 c) 2 +
      minusCoordinates 2 (minusCoordinates 2 c) 2 = -8 * c 2 := by
  simp; ring

private theorem minus_coordinate_casimir_3 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 3 +
      minusCoordinates 1 (minusCoordinates 1 c) 3 +
      minusCoordinates 2 (minusCoordinates 2 c) 3 = -8 * c 3 := by
  simp; ring

private theorem minus_coordinate_casimir_4 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 4 +
      minusCoordinates 1 (minusCoordinates 1 c) 4 +
      minusCoordinates 2 (minusCoordinates 2 c) 4 = -8 * c 4 := by
  simp; ring

private theorem minus_coordinate_casimir_5 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 5 +
      minusCoordinates 1 (minusCoordinates 1 c) 5 +
      minusCoordinates 2 (minusCoordinates 2 c) 5 = -8 * c 5 := by
  simp; ring

private theorem minus_coordinate_casimir_6 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 6 +
      minusCoordinates 1 (minusCoordinates 1 c) 6 +
      minusCoordinates 2 (minusCoordinates 2 c) 6 = -8 * c 6 := by
  simp; ring

private theorem minus_coordinate_casimir_7 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 7 +
      minusCoordinates 1 (minusCoordinates 1 c) 7 +
      minusCoordinates 2 (minusCoordinates 2 c) 7 = -8 * c 7 := by
  simp; ring

private theorem minus_coordinate_casimir_8 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 8 +
      minusCoordinates 1 (minusCoordinates 1 c) 8 +
      minusCoordinates 2 (minusCoordinates 2 c) 8 = -8 * c 8 := by
  simp; ring

private theorem minus_coordinate_casimir_9 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 9 +
      minusCoordinates 1 (minusCoordinates 1 c) 9 +
      minusCoordinates 2 (minusCoordinates 2 c) 9 = -8 * c 9 := by
  simp; ring

private theorem minus_coordinate_casimir_10 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 10 +
      minusCoordinates 1 (minusCoordinates 1 c) 10 +
      minusCoordinates 2 (minusCoordinates 2 c) 10 = -8 * c 10 := by
  simp; ring

private theorem minus_coordinate_casimir_11 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 11 +
      minusCoordinates 1 (minusCoordinates 1 c) 11 +
      minusCoordinates 2 (minusCoordinates 2 c) 11 = -8 * c 11 := by
  simp; ring

private theorem minus_coordinate_casimir_12 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 12 +
      minusCoordinates 1 (minusCoordinates 1 c) 12 +
      minusCoordinates 2 (minusCoordinates 2 c) 12 = -8 * c 12 := by
  simp; ring

private theorem minus_coordinate_casimir_13 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 13 +
      minusCoordinates 1 (minusCoordinates 1 c) 13 +
      minusCoordinates 2 (minusCoordinates 2 c) 13 = -8 * c 13 := by
  simp; ring

private theorem minus_coordinate_casimir_14 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 14 +
      minusCoordinates 1 (minusCoordinates 1 c) 14 +
      minusCoordinates 2 (minusCoordinates 2 c) 14 = -8 * c 14 := by
  simp; ring

private theorem minus_coordinate_casimir_15 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 15 +
      minusCoordinates 1 (minusCoordinates 1 c) 15 +
      minusCoordinates 2 (minusCoordinates 2 c) 15 = -8 * c 15 := by
  simp; ring

private theorem minus_coordinate_casimir_16 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 16 +
      minusCoordinates 1 (minusCoordinates 1 c) 16 +
      minusCoordinates 2 (minusCoordinates 2 c) 16 = -8 * c 16 := by
  simp; ring

private theorem minus_coordinate_casimir_17 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 17 +
      minusCoordinates 1 (minusCoordinates 1 c) 17 +
      minusCoordinates 2 (minusCoordinates 2 c) 17 = -8 * c 17 := by
  simp; ring

private theorem minus_coordinate_casimir_18 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 18 +
      minusCoordinates 1 (minusCoordinates 1 c) 18 +
      minusCoordinates 2 (minusCoordinates 2 c) 18 = -8 * c 18 := by
  simp; ring

private theorem minus_coordinate_casimir_19 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 19 +
      minusCoordinates 1 (minusCoordinates 1 c) 19 +
      minusCoordinates 2 (minusCoordinates 2 c) 19 = -8 * c 19 := by
  simp; ring

private theorem minus_coordinate_casimir_20 (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) 20 +
      minusCoordinates 1 (minusCoordinates 1 c) 20 +
      minusCoordinates 2 (minusCoordinates 2 c) 20 = -8 * c 20 := by
  simp; ring

theorem minus_coordinate_casimir (c : Fin 21 → ℝ) :
    minusCoordinates 0 (minusCoordinates 0 c) +
      minusCoordinates 1 (minusCoordinates 1 c) +
      minusCoordinates 2 (minusCoordinates 2 c) = (-8 : ℝ) • c := by
  funext k
  fin_cases k
  · exact minus_coordinate_casimir_0 c
  · exact minus_coordinate_casimir_1 c
  · exact minus_coordinate_casimir_2 c
  · exact minus_coordinate_casimir_3 c
  · exact minus_coordinate_casimir_4 c
  · exact minus_coordinate_casimir_5 c
  · exact minus_coordinate_casimir_6 c
  · exact minus_coordinate_casimir_7 c
  · exact minus_coordinate_casimir_8 c
  · exact minus_coordinate_casimir_9 c
  · exact minus_coordinate_casimir_10 c
  · exact minus_coordinate_casimir_11 c
  · exact minus_coordinate_casimir_12 c
  · exact minus_coordinate_casimir_13 c
  · exact minus_coordinate_casimir_14 c
  · exact minus_coordinate_casimir_15 c
  · exact minus_coordinate_casimir_16 c
  · exact minus_coordinate_casimir_17 c
  · exact minus_coordinate_casimir_18 c
  · exact minus_coordinate_casimir_19 c
  · exact minus_coordinate_casimir_20 c


end
end PositiveEinsteinFour.HighestHessian

end OAI
