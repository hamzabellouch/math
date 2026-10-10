import OAI.Geometry.EinsteinFour.HighestSquare

namespace OAI

/-! The trace lift intertwines the actual tensor rotation actions. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators
open HighestHessian

private theorem traceLift_plus_0_0_0 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 0 0 a b =
      traceLift (matrixAction 0 M) 0 0 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_0_1 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 0 1 a b =
      traceLift (matrixAction 0 M) 0 1 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_0_2 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 0 2 a b =
      traceLift (matrixAction 0 M) 0 2 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_0_3 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 0 3 a b =
      traceLift (matrixAction 0 M) 0 3 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_0 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 0 j a b = traceLift (matrixAction 0 M) 0 j a b := by
  fin_cases j
  · exact traceLift_plus_0_0_0 M a b
  · exact traceLift_plus_0_0_1 M a b
  · exact traceLift_plus_0_0_2 M a b
  · exact traceLift_plus_0_0_3 M a b

private theorem traceLift_plus_0_1_0 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 1 0 a b =
      traceLift (matrixAction 0 M) 1 0 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_1_1 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 1 1 a b =
      traceLift (matrixAction 0 M) 1 1 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_1_2 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 1 2 a b =
      traceLift (matrixAction 0 M) 1 2 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_1_3 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 1 3 a b =
      traceLift (matrixAction 0 M) 1 3 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_1 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 1 j a b = traceLift (matrixAction 0 M) 1 j a b := by
  fin_cases j
  · exact traceLift_plus_0_1_0 M a b
  · exact traceLift_plus_0_1_1 M a b
  · exact traceLift_plus_0_1_2 M a b
  · exact traceLift_plus_0_1_3 M a b

private theorem traceLift_plus_0_2_0 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 2 0 a b =
      traceLift (matrixAction 0 M) 2 0 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_2_1 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 2 1 a b =
      traceLift (matrixAction 0 M) 2 1 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_2_2 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 2 2 a b =
      traceLift (matrixAction 0 M) 2 2 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_2_3 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 2 3 a b =
      traceLift (matrixAction 0 M) 2 3 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_2 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 2 j a b = traceLift (matrixAction 0 M) 2 j a b := by
  fin_cases j
  · exact traceLift_plus_0_2_0 M a b
  · exact traceLift_plus_0_2_1 M a b
  · exact traceLift_plus_0_2_2 M a b
  · exact traceLift_plus_0_2_3 M a b

private theorem traceLift_plus_0_3_0 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 3 0 a b =
      traceLift (matrixAction 0 M) 3 0 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_3_1 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 3 1 a b =
      traceLift (matrixAction 0 M) 3 1 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_3_2 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 3 2 a b =
      traceLift (matrixAction 0 M) 3 2 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_3_3 (M : Mat) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 3 3 a b =
      traceLift (matrixAction 0 M) 3 3 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_0_3 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalPlus 0 (traceLift M) 3 j a b = traceLift (matrixAction 0 M) 3 j a b := by
  fin_cases j
  · exact traceLift_plus_0_3_0 M a b
  · exact traceLift_plus_0_3_1 M a b
  · exact traceLift_plus_0_3_2 M a b
  · exact traceLift_plus_0_3_3 M a b

private theorem traceLift_plus_1_0_0 (M : Mat) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 0 0 a b =
      traceLift (matrixAction 1 M) 0 0 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_1_0_1 (M : Mat) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 0 1 a b =
      traceLift (matrixAction 1 M) 0 1 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_1_0_2 (M : Mat) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 0 2 a b =
      traceLift (matrixAction 1 M) 0 2 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_1_0_3 (M : Mat) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 0 3 a b =
      traceLift (matrixAction 1 M) 0 3 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_1_0 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 0 j a b = traceLift (matrixAction 1 M) 0 j a b := by
  fin_cases j
  · exact traceLift_plus_1_0_0 M a b
  · exact traceLift_plus_1_0_1 M a b
  · exact traceLift_plus_1_0_2 M a b
  · exact traceLift_plus_1_0_3 M a b

private theorem traceLift_plus_1_1_0 (M : Mat) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 1 0 a b =
      traceLift (matrixAction 1 M) 1 0 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_1_1_1 (M : Mat) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 1 1 a b =
      traceLift (matrixAction 1 M) 1 1 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_1_1_2 (M : Mat) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 1 2 a b =
      traceLift (matrixAction 1 M) 1 2 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_1_1_3 (M : Mat) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 1 3 a b =
      traceLift (matrixAction 1 M) 1 3 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_1_1 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 1 j a b = traceLift (matrixAction 1 M) 1 j a b := by
  fin_cases j
  · exact traceLift_plus_1_1_0 M a b
  · exact traceLift_plus_1_1_1 M a b
  · exact traceLift_plus_1_1_2 M a b
  · exact traceLift_plus_1_1_3 M a b

private theorem traceLift_plus_1_2_0 (M : Mat) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 2 0 a b =
      traceLift (matrixAction 1 M) 2 0 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_1_2_1 (M : Mat) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 2 1 a b =
      traceLift (matrixAction 1 M) 2 1 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_1_2_2 (M : Mat) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 2 2 a b =
      traceLift (matrixAction 1 M) 2 2 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_1_2_3 (M : Mat) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 2 3 a b =
      traceLift (matrixAction 1 M) 2 3 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_1_2 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 2 j a b = traceLift (matrixAction 1 M) 2 j a b := by
  fin_cases j
  · exact traceLift_plus_1_2_0 M a b
  · exact traceLift_plus_1_2_1 M a b
  · exact traceLift_plus_1_2_2 M a b
  · exact traceLift_plus_1_2_3 M a b

private theorem traceLift_plus_1_3_0 (M : Mat) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 3 0 a b =
      traceLift (matrixAction 1 M) 3 0 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_1_3_1 (M : Mat) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 3 1 a b =
      traceLift (matrixAction 1 M) 3 1 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_1_3_2 (M : Mat) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 3 2 a b =
      traceLift (matrixAction 1 M) 3 2 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_1_3_3 (M : Mat) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 3 3 a b =
      traceLift (matrixAction 1 M) 3 3 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_1_3 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalPlus 1 (traceLift M) 3 j a b = traceLift (matrixAction 1 M) 3 j a b := by
  fin_cases j
  · exact traceLift_plus_1_3_0 M a b
  · exact traceLift_plus_1_3_1 M a b
  · exact traceLift_plus_1_3_2 M a b
  · exact traceLift_plus_1_3_3 M a b

private theorem traceLift_plus_2_0_0 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 0 0 a b =
      traceLift (matrixAction 2 M) 0 0 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_0_1 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 0 1 a b =
      traceLift (matrixAction 2 M) 0 1 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_0_2 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 0 2 a b =
      traceLift (matrixAction 2 M) 0 2 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_0_3 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 0 3 a b =
      traceLift (matrixAction 2 M) 0 3 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_0 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 0 j a b = traceLift (matrixAction 2 M) 0 j a b := by
  fin_cases j
  · exact traceLift_plus_2_0_0 M a b
  · exact traceLift_plus_2_0_1 M a b
  · exact traceLift_plus_2_0_2 M a b
  · exact traceLift_plus_2_0_3 M a b

private theorem traceLift_plus_2_1_0 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 1 0 a b =
      traceLift (matrixAction 2 M) 1 0 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_1_1 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 1 1 a b =
      traceLift (matrixAction 2 M) 1 1 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_1_2 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 1 2 a b =
      traceLift (matrixAction 2 M) 1 2 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_1_3 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 1 3 a b =
      traceLift (matrixAction 2 M) 1 3 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_1 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 1 j a b = traceLift (matrixAction 2 M) 1 j a b := by
  fin_cases j
  · exact traceLift_plus_2_1_0 M a b
  · exact traceLift_plus_2_1_1 M a b
  · exact traceLift_plus_2_1_2 M a b
  · exact traceLift_plus_2_1_3 M a b

private theorem traceLift_plus_2_2_0 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 2 0 a b =
      traceLift (matrixAction 2 M) 2 0 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_2_1 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 2 1 a b =
      traceLift (matrixAction 2 M) 2 1 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_2_2 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 2 2 a b =
      traceLift (matrixAction 2 M) 2 2 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_2_3 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 2 3 a b =
      traceLift (matrixAction 2 M) 2 3 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_2 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 2 j a b = traceLift (matrixAction 2 M) 2 j a b := by
  fin_cases j
  · exact traceLift_plus_2_2_0 M a b
  · exact traceLift_plus_2_2_1 M a b
  · exact traceLift_plus_2_2_2 M a b
  · exact traceLift_plus_2_2_3 M a b

private theorem traceLift_plus_2_3_0 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 3 0 a b =
      traceLift (matrixAction 2 M) 3 0 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_3_1 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 3 1 a b =
      traceLift (matrixAction 2 M) 3 1 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_3_2 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 3 2 a b =
      traceLift (matrixAction 2 M) 3 2 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_3_3 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 3 3 a b =
      traceLift (matrixAction 2 M) 3 3 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [totalPlus, traceLift, matrixAction, rotation, quaternionMatrix,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_plus_2_3 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 3 j a b = traceLift (matrixAction 2 M) 3 j a b := by
  fin_cases j
  · exact traceLift_plus_2_3_0 M a b
  · exact traceLift_plus_2_3_1 M a b
  · exact traceLift_plus_2_3_2 M a b
  · exact traceLift_plus_2_3_3 M a b

private theorem traceLift_minus_0_0 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalMinus 0 (traceLift M) 0 j a b = 0 := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [totalMinus, traceLift, matrixAction, rotation, quaternionMatrix, rightQuaternion,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_minus_0_1 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalMinus 0 (traceLift M) 1 j a b = 0 := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [totalMinus, traceLift, matrixAction, rotation, quaternionMatrix, rightQuaternion,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_minus_0_2 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalMinus 0 (traceLift M) 2 j a b = 0 := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [totalMinus, traceLift, matrixAction, rotation, quaternionMatrix, rightQuaternion,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_minus_0_3 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalMinus 0 (traceLift M) 3 j a b = 0 := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [totalMinus, traceLift, matrixAction, rotation, quaternionMatrix, rightQuaternion,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_minus_1_0 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalMinus 1 (traceLift M) 0 j a b = 0 := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [totalMinus, traceLift, matrixAction, rotation, quaternionMatrix, rightQuaternion,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_minus_1_1 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalMinus 1 (traceLift M) 1 j a b = 0 := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [totalMinus, traceLift, matrixAction, rotation, quaternionMatrix, rightQuaternion,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_minus_1_2 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalMinus 1 (traceLift M) 2 j a b = 0 := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [totalMinus, traceLift, matrixAction, rotation, quaternionMatrix, rightQuaternion,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_minus_1_3 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalMinus 1 (traceLift M) 3 j a b = 0 := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [totalMinus, traceLift, matrixAction, rotation, quaternionMatrix, rightQuaternion,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_minus_2_0 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalMinus 2 (traceLift M) 0 j a b = 0 := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [totalMinus, traceLift, matrixAction, rotation, quaternionMatrix, rightQuaternion,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_minus_2_1 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalMinus 2 (traceLift M) 1 j a b = 0 := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [totalMinus, traceLift, matrixAction, rotation, quaternionMatrix, rightQuaternion,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_minus_2_2 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalMinus 2 (traceLift M) 2 j a b = 0 := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [totalMinus, traceLift, matrixAction, rotation, quaternionMatrix, rightQuaternion,
      Fin.sum_univ_succ]
  all_goals ring

private theorem traceLift_minus_2_3 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalMinus 2 (traceLift M) 3 j a b = 0 := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [totalMinus, traceLift, matrixAction, rotation, quaternionMatrix, rightQuaternion,
      Fin.sum_univ_succ]
  all_goals ring

/-- The plus tensor action on the explicit restricted trace adjoint. -/
theorem totalPlus_traceLift (s : Fin 3) (M : Mat) :
    totalPlus s (traceLift M) = traceLift (matrixAction s M) := by
  funext i j a b
  fin_cases s <;> fin_cases i
  · exact traceLift_plus_0_0 M j a b
  · exact traceLift_plus_0_1 M j a b
  · exact traceLift_plus_0_2 M j a b
  · exact traceLift_plus_0_3 M j a b
  · exact traceLift_plus_1_0 M j a b
  · exact traceLift_plus_1_1 M j a b
  · exact traceLift_plus_1_2 M j a b
  · exact traceLift_plus_1_3 M j a b
  · exact traceLift_plus_2_0 M j a b
  · exact traceLift_plus_2_1 M j a b
  · exact traceLift_plus_2_2 M j a b
  · exact traceLift_plus_2_3 M j a b

/-- The minus tensor action on the explicit restricted trace adjoint. -/
theorem totalMinus_traceLift (s : Fin 3) (M : Mat) :
    totalMinus s (traceLift M) = 0 := by
  funext i j a b
  fin_cases s <;> fin_cases i
  · exact traceLift_minus_0_0 M j a b
  · exact traceLift_minus_0_1 M j a b
  · exact traceLift_minus_0_2 M j a b
  · exact traceLift_minus_0_3 M j a b
  · exact traceLift_minus_1_0 M j a b
  · exact traceLift_minus_1_1 M j a b
  · exact traceLift_minus_1_2 M j a b
  · exact traceLift_minus_1_3 M j a b
  · exact traceLift_minus_2_0 M j a b
  · exact traceLift_minus_2_1 M j a b
  · exact traceLift_minus_2_2 M j a b
  · exact traceLift_minus_2_3 M j a b

end
end PositiveEinsteinFour.TraceHessian

end OAI
