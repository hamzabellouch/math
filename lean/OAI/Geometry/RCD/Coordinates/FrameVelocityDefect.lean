import OAI.Geometry.RCD.Coordinates.FrameResidualDefect

namespace OAI

/-! # Quantitative scalar velocity recovery from dense residual tests -/

open Set
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates

theorem velocity_defect_of_dense_residual_bounds {n : ℕ}
    (a v : Euclidean n) (w D E G : ℝ) {S : Set (Euclidean n)} (hS : Dense S)
    (h : ∀ b∈S, (w-⟪b,v⟫_ℝ)^2≤D^2*(‖a-b‖^2+E+G*‖b‖^2)) :
    (w-⟪a,v⟫_ℝ)^2≤D^2*(E+G*‖a‖^2) := by
  have hc : IsClosed {b : Euclidean n |
      (w-⟪b,v⟫_ℝ)^2≤D^2*(‖a-b‖^2+E+G*‖b‖^2)} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hall := closure_minimal h hc
  rw [hS.closure_eq] at hall
  have ha := hall (mem_univ a)
  change (w-⟪a,v⟫_ℝ)^2≤D^2*(‖a-a‖^2+E+G*‖a‖^2) at ha
  simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_add] using ha

theorem scalar_velocity_abs_error {n : ℕ} (a v : Euclidean n) (w D E G : ℝ)
    (hD : 0≤D) (hE : 0≤E) (hG : 0≤G)
    (h : (w-⟪a,v⟫_ℝ)^2≤D^2*(E+G*‖a‖^2)) :
    |w-⟪a,v⟫_ℝ|≤D*Real.sqrt (E+G*‖a‖^2) := by
  have hp : 0≤E+G*‖a‖^2 := add_nonneg hE (mul_nonneg hG (sq_nonneg _))
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hD (Real.sqrt_nonneg _))).mp
  simpa only [sq_abs,mul_pow,Real.sq_sqrt hp] using h

end RegularPointCoordinates

end

end OAI
