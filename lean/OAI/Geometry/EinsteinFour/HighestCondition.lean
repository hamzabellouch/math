import OAI.Geometry.EinsteinFour.HighestHessian

namespace OAI

/-! The displayed highest coordinates satisfy every original tensor constraint. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- Symmetry is built into the two derivative slots of the coordinate array. -/
theorem highest_derivative_symmetric (c : Fin 21 → ℝ) (i j : Fin 4) :
    highest c i j = highest c j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem highest_matrix_symmetric (c : Fin 21 → ℝ) (i j : Fin 4) :
    symmetric (highest c i j) := by
  intro a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [ofCoordinates]

theorem highest_matrix_traceFree (c : Fin 21 → ℝ) (i j : Fin 4) :
    traceFree (highest c i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [traceFree, ofCoordinates, Fin.sum_univ_succ]
  all_goals ring

theorem highest_trace (c : Fin 21 → ℝ) : hessianTrace (highest c) = 0 := by
  ext a b
  change (∑ i, highest c i i a b) = 0
  fin_cases a <;> fin_cases b <;>
    simp [ofCoordinates, Fin.sum_univ_succ]
  all_goals ring

theorem highest_divergence (c : Fin 21 → ℝ) (i : Fin 4) (r : Fin 3) :
    divergence (highest c) i r = 0 := by
  ext u
  fin_cases i <;> fin_cases r <;> fin_cases u <;>
    simp [divergence, quaternion, Fin.sum_univ_succ]
  all_goals simp [ofCoordinates]
  all_goals ring

/-- The concrete constrained-space description in both directions. -/
theorem highest_condition (c : Fin 21 → ℝ) : condition (highest c) := by
  refine ⟨highest_derivative_symmetric c, ?_, highest_trace c, highest_divergence c⟩
  intro i j
  exact ⟨highest_matrix_symmetric c i j, highest_matrix_traceFree c i j⟩

theorem condition_iff_exists_highest (X : Hessian) :
    condition X ↔ ∃ c : Fin 21 → ℝ, highest c = X := by
  constructor
  · exact exists_highest X
  · rintro ⟨c, rfl⟩
    exact highest_condition c

end
end PositiveEinsteinFour.HighestHessian

end OAI
