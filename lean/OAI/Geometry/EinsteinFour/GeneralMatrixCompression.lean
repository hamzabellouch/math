import OAI.Geometry.EinsteinFour.GradientCoordinateModel
import OAI.Geometry.EinsteinFour.GradientPairing
import OAI.Geometry.EinsteinFour.MatrixSlotOperator

namespace OAI

/-! Bianchi compression for an arbitrary symmetric trace-free Weyl matrix,
with no choice of a moving diagonal frame. -/

namespace PositiveEinsteinFour.Bianchi

open scoped BigOperators
open TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- The actual trace-free anticommutator, acting on the two matrix indices. -/
def generalMatrixAction (A : Mat) (Z : RawGradient) : RawGradient :=
  fun a b => WithLp.toLp 2 (fun j => matrixSlotAction A (fun c d => Z c d j) a b)

/-- Mixed derivative/matrix action, retaining the full matrix of coefficients. -/
def generalMixedAction (A : Mat) (Z : RawGradient) : RawGradient :=
  fun a b => ∑ r, ∑ s, A r s • quaternion r (rawMatrixRotation s Z a b)


private def costMatrix (v : Fin 3 → Vec) : RawGradient :=
  ![![-v 0 + (3 : ℝ) • v 1,
      -quaternion 2 (v 2 + (2 : ℝ) • v 1),
      -quaternion 1 (v 2 - v 1 + v 0)],
    ![-quaternion 2 (v 2 + (2 : ℝ) • v 1),
      -v 0 - (3 : ℝ) • v 1,
      -quaternion 0 (v 2 - v 1 - v 0)],
    ![-quaternion 1 (v 2 - v 1 + v 0),
      -quaternion 0 (v 2 - v 1 - v 0), (2 : ℝ) • v 0]]

private theorem costParameters_matrix_eq_0_0 (v : Fin 3 → Vec) :
    (costParameters v).matrix 0 0 = costMatrix v 0 0 := by
  ext u
  fin_cases u <;>
    simp [costParameters, costMatrix, parameters, costShape,
      Tensor.matrix, difference, next, previous, quaternion]
  all_goals ring

private theorem costParameters_matrix_eq_0_1 (v : Fin 3 → Vec) :
    (costParameters v).matrix 0 1 = costMatrix v 0 1 := by
  ext u
  fin_cases u <;>
    simp [costParameters, costMatrix, parameters, costShape,
      Tensor.matrix, difference, next, previous, quaternion]

private theorem costParameters_matrix_eq_0_2 (v : Fin 3 → Vec) :
    (costParameters v).matrix 0 2 = costMatrix v 0 2 := by
  ext u
  fin_cases u <;>
    simp [costParameters, costMatrix, parameters, costShape,
      Tensor.matrix, difference, next, previous, quaternion]
  all_goals ring

private theorem costParameters_matrix_eq_1_0 (v : Fin 3 → Vec) :
    (costParameters v).matrix 1 0 = costMatrix v 1 0 := by
  ext u
  fin_cases u <;>
    simp [costParameters, costMatrix, parameters, costShape,
      Tensor.matrix, difference, next, previous, quaternion]

private theorem costParameters_matrix_eq_1_1 (v : Fin 3 → Vec) :
    (costParameters v).matrix 1 1 = costMatrix v 1 1 := by
  ext u
  fin_cases u <;>
    simp [costParameters, costMatrix, parameters, costShape,
      Tensor.matrix, difference, next, previous, quaternion]
  all_goals exact Or.inl (by norm_num)

private theorem costParameters_matrix_eq_1_2 (v : Fin 3 → Vec) :
    (costParameters v).matrix 1 2 = costMatrix v 1 2 := by
  ext u
  fin_cases u <;>
    simp [costParameters, costMatrix, parameters, costShape,
      Tensor.matrix, difference, next, previous, quaternion]
  all_goals ring

private theorem costParameters_matrix_eq_2_0 (v : Fin 3 → Vec) :
    (costParameters v).matrix 2 0 = costMatrix v 2 0 := by
  ext u
  fin_cases u <;>
    simp [costParameters, costMatrix, parameters, costShape,
      Tensor.matrix, difference, next, previous, quaternion]
  all_goals ring

private theorem costParameters_matrix_eq_2_1 (v : Fin 3 → Vec) :
    (costParameters v).matrix 2 1 = costMatrix v 2 1 := by
  ext u
  fin_cases u <;>
    simp [costParameters, costMatrix, parameters, costShape,
      Tensor.matrix, difference, next, previous, quaternion]
  all_goals ring

private theorem costParameters_matrix_eq_2_2 (v : Fin 3 → Vec) :
    (costParameters v).matrix 2 2 = costMatrix v 2 2 := by
  ext u
  fin_cases u <;>
    simp [costParameters, costMatrix, parameters, costShape,
      Tensor.matrix, difference, next, previous, quaternion]

private theorem costParameters_matrix_eq (v : Fin 3 → Vec) :
    (costParameters v).matrix = costMatrix v := by
  funext i j
  fin_cases i <;> fin_cases j
  · exact costParameters_matrix_eq_0_0 v
  · exact costParameters_matrix_eq_0_1 v
  · exact costParameters_matrix_eq_0_2 v
  · exact costParameters_matrix_eq_1_0 v
  · exact costParameters_matrix_eq_1_1 v
  · exact costParameters_matrix_eq_1_2 v
  · exact costParameters_matrix_eq_2_0 v
  · exact costParameters_matrix_eq_2_1 v
  · exact costParameters_matrix_eq_2_2 v


private theorem coupling_matrix_coordinates_0_0_0
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 0 0 0 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 0 0) 0 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_0_0_1
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 0 0 1 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 0 0) 1 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_0_0_2
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 0 0 2 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 0 0) 2 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_0_0_3
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 0 0 3 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 0 0) 3 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_0_0
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 0 0 =
      (-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 0 0 := by
  ext u
  fin_cases u
  · exact coupling_matrix_coordinates_0_0_0 a b c d e v
  · exact coupling_matrix_coordinates_0_0_1 a b c d e v
  · exact coupling_matrix_coordinates_0_0_2 a b c d e v
  · exact coupling_matrix_coordinates_0_0_3 a b c d e v

private theorem coupling_matrix_coordinates_0_1_0
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 0 1 0 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 0 1) 0 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_0_1_1
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 0 1 1 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 0 1) 1 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_0_1_2
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 0 1 2 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 0 1) 2 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_0_1_3
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 0 1 3 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 0 1) 3 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_0_1
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 0 1 =
      (-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 0 1 := by
  ext u
  fin_cases u
  · exact coupling_matrix_coordinates_0_1_0 a b c d e v
  · exact coupling_matrix_coordinates_0_1_1 a b c d e v
  · exact coupling_matrix_coordinates_0_1_2 a b c d e v
  · exact coupling_matrix_coordinates_0_1_3 a b c d e v

private theorem coupling_matrix_coordinates_0_2_0
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 0 2 0 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 0 2) 0 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_0_2_1
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 0 2 1 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 0 2) 1 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_0_2_2
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 0 2 2 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 0 2) 2 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_0_2_3
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 0 2 3 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 0 2) 3 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_0_2
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 0 2 =
      (-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 0 2 := by
  ext u
  fin_cases u
  · exact coupling_matrix_coordinates_0_2_0 a b c d e v
  · exact coupling_matrix_coordinates_0_2_1 a b c d e v
  · exact coupling_matrix_coordinates_0_2_2 a b c d e v
  · exact coupling_matrix_coordinates_0_2_3 a b c d e v

private theorem coupling_matrix_coordinates_1_0_0
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 1 0 0 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 1 0) 0 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_1_0_1
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 1 0 1 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 1 0) 1 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_1_0_2
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 1 0 2 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 1 0) 2 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_1_0_3
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 1 0 3 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 1 0) 3 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_1_0
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 1 0 =
      (-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 1 0 := by
  ext u
  fin_cases u
  · exact coupling_matrix_coordinates_1_0_0 a b c d e v
  · exact coupling_matrix_coordinates_1_0_1 a b c d e v
  · exact coupling_matrix_coordinates_1_0_2 a b c d e v
  · exact coupling_matrix_coordinates_1_0_3 a b c d e v

private theorem coupling_matrix_coordinates_1_1_0
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 1 1 0 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 1 1) 0 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_1_1_1
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 1 1 1 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 1 1) 1 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_1_1_2
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 1 1 2 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 1 1) 2 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_1_1_3
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 1 1 3 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 1 1) 3 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_1_1
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 1 1 =
      (-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 1 1 := by
  ext u
  fin_cases u
  · exact coupling_matrix_coordinates_1_1_0 a b c d e v
  · exact coupling_matrix_coordinates_1_1_1 a b c d e v
  · exact coupling_matrix_coordinates_1_1_2 a b c d e v
  · exact coupling_matrix_coordinates_1_1_3 a b c d e v

private theorem coupling_matrix_coordinates_1_2_0
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 1 2 0 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 1 2) 0 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_1_2_1
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 1 2 1 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 1 2) 1 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_1_2_2
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 1 2 2 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 1 2) 2 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_1_2_3
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 1 2 3 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 1 2) 3 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_1_2
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 1 2 =
      (-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 1 2 := by
  ext u
  fin_cases u
  · exact coupling_matrix_coordinates_1_2_0 a b c d e v
  · exact coupling_matrix_coordinates_1_2_1 a b c d e v
  · exact coupling_matrix_coordinates_1_2_2 a b c d e v
  · exact coupling_matrix_coordinates_1_2_3 a b c d e v

private theorem coupling_matrix_coordinates_2_0_0
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 0 0 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 0) 0 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_2_0_1
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 0 1 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 0) 1 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_2_0_2
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 0 2 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 0) 2 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_2_0_3
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 0 3 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 0) 3 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_2_0
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 0 =
      (-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 0 := by
  ext u
  fin_cases u
  · exact coupling_matrix_coordinates_2_0_0 a b c d e v
  · exact coupling_matrix_coordinates_2_0_1 a b c d e v
  · exact coupling_matrix_coordinates_2_0_2 a b c d e v
  · exact coupling_matrix_coordinates_2_0_3 a b c d e v

private theorem coupling_matrix_coordinates_2_1_0
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 1 0 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 1) 0 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_2_1_1
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 1 1 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 1) 1 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_2_1_2
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 1 2 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 1) 2 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_2_1_3
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 1 3 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 1) 3 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_2_1
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 1 =
      (-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 1 := by
  ext u
  fin_cases u
  · exact coupling_matrix_coordinates_2_1_0 a b c d e v
  · exact coupling_matrix_coordinates_2_1_1 a b c d e v
  · exact coupling_matrix_coordinates_2_1_2 a b c d e v
  · exact coupling_matrix_coordinates_2_1_3 a b c d e v

private theorem coupling_matrix_coordinates_2_2_0
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 2 0 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 2) 0 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_2_2_1
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 2 1 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 2) 1 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_2_2_2
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 2 2 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 2) 2 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_2_2_3
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 2 3 =
      ((-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 2) 3 := by
  rw [costParameters_matrix_eq]
  simp [rawCoupling, generalMatrixAction, generalMixedAction, matrixSlotAction,
    rawMatrixRotation, ofCoordinates, costMatrix, TraceHessian.rotation,
    quaternion, Fin.sum_univ_succ]
  ring

private theorem coupling_matrix_coordinates_2_2
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 2 =
      (-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 2 := by
  ext u
  fin_cases u
  · exact coupling_matrix_coordinates_2_2_0 a b c d e v
  · exact coupling_matrix_coordinates_2_2_1 a b c d e v
  · exact coupling_matrix_coordinates_2_2_2 a b c d e v
  · exact coupling_matrix_coordinates_2_2_3 a b c d e v


private theorem coupling_matrix_coordinates
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) =
      (-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix := by
  funext i j
  fin_cases i <;> fin_cases j
  · exact coupling_matrix_coordinates_0_0 a b c d e v
  · exact coupling_matrix_coordinates_0_1 a b c d e v
  · exact coupling_matrix_coordinates_0_2 a b c d e v
  · exact coupling_matrix_coordinates_1_0 a b c d e v
  · exact coupling_matrix_coordinates_1_1 a b c d e v
  · exact coupling_matrix_coordinates_1_2 a b c d e v
  · exact coupling_matrix_coordinates_2_0 a b c d e v
  · exact coupling_matrix_coordinates_2_1 a b c d e v
  · exact coupling_matrix_coordinates_2_2 a b c d e v

/-- The full coefficient matrix satisfies the same coupling identity as
the diagonal specialization. The proof uses the actual twelve-dimensional
Bianchi coordinates and the five free entries of the symmetric matrix. -/
theorem rawCoupling_generalMatrixAction (A : Mat)
    (hA : symmetric A) (hAt : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    rawCoupling (generalMatrixAction A Z.matrix) =
      (-(1 / 2 : ℝ)) • generalMixedAction A Z.matrix := by
  obtain ⟨v, rfl⟩ := exists_costParameters Z hz hb
  rw [← coordinates_eq A hA hAt]
  exact coupling_matrix_coordinates _ _ _ _ _ v

/-- Bilinear compression against any Bianchi test tensor. No pointwise
diagonal frame is assumed for either the Weyl coefficient or the test. -/
theorem generalMixedAction_pairing (A : Mat)
    (hA : symmetric A) (hAt : traceFree A)
    (Z W : Tensor) (hz : Z.traceFree) (hbz : Z.bianchi) (hbw : W.bianchi) :
    rawPairing (generalMixedAction A Z.matrix) W.matrix =
      8 * rawPairing (generalMatrixAction A Z.matrix) W.matrix := by
  have hW : rawCoupling W.matrix = (-4 : ℝ) • W.matrix := by
    funext a b
    exact gradientCoupling_eq W hbw a b
  have h := rawCoupling_selfadjoint (generalMatrixAction A Z.matrix) W.matrix
  rw [rawCoupling_generalMatrixAction A hA hAt Z hz hbz, hW,
    rawPairing_smul_left, rawPairing_smul_right] at h
  linarith

/-- The polynomial formula for the actual orthogonal Bianchi compression. -/
def rawBianchiProjection (Z : RawGradient) : RawGradient :=
  (1 / 10 : ℝ) • ((6 : ℝ) • Z - rawCoupling Z)

theorem rawBianchiProjection_pairing (Z : RawGradient) (W : Tensor) (hbw : W.bianchi) :
    rawPairing (rawBianchiProjection Z) W.matrix = rawPairing Z W.matrix := by
  have hW : rawCoupling W.matrix = (-4 : ℝ) • W.matrix := by
    funext a b
    exact gradientCoupling_eq W hbw a b
  unfold rawBianchiProjection
  rw [rawPairing_smul_left, rawPairing_sub_left, rawPairing_smul_left,
    rawCoupling_selfadjoint, hW, rawPairing_smul_right]
  ring

/-- The uncompressed Ricci expression equals 13Z−20P(B_F(A)Z) as
an actual four-vector-valued array, for arbitrary Weyl coefficients. -/
theorem generalRicci_compression (A : Mat)
    (hA : symmetric A) (hAt : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    (13 : ℝ) • Z.matrix - (12 : ℝ) • generalMatrixAction A Z.matrix -
        generalMixedAction A Z.matrix =
      (13 : ℝ) • Z.matrix -
        (20 : ℝ) • rawBianchiProjection (generalMatrixAction A Z.matrix) := by
  unfold rawBianchiProjection
  rw [rawCoupling_generalMatrixAction A hA hAt Z hz hb]
  module

end
end PositiveEinsteinFour.Bianchi

end OAI
