import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic

namespace OAI

/-!
# Directional estimates for positive local mass forms

These are the two positive-matrix inequalities in `re:positive-matrix-bound`,
in coordinates where the frozen metric is the identity. Positivity permits
singular mass forms; no inverse of a local mass matrix is used.
-/

open scoped InnerProductSpace

namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Cauchy--Schwarz for a possibly degenerate positive quadratic form. -/
theorem positive_form_cauchy_schwarz {D : E →L[ℝ] E} (hD : D.IsPositive) (x y : E) :
    ⟪x, D y⟫_ℝ ^ 2 ≤ ⟪x, D x⟫_ℝ * ⟪y, D y⟫_ℝ := by
  have hsym : ⟪y, D x⟫_ℝ = ⟪x, D y⟫_ℝ := by
    rw [real_inner_comm, hD.inner_left_eq_inner_right]
  have hpoly : ∀ t : ℝ,
      0 ≤ ⟪y, D y⟫_ℝ * (t * t) + (2 * ⟪x, D y⟫_ℝ) * t + ⟪x, D x⟫_ℝ := by
    intro t
    have h := hD.inner_nonneg_right (x + t • y)
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, conj_trivial, hsym] at h
    nlinarith
  have hdisc := discrim_le_zero hpoly
  unfold discrim at hdisc
  nlinarith

/-- The directional Cauchy--Schwarz inequality in the form used for cutoffs. -/
theorem positive_form_inner_abs_le {D : E →L[ℝ] E} (hD : D.IsPositive) (x y : E) :
    |⟪x, D y⟫_ℝ| ≤ Real.sqrt ⟪x, D x⟫_ℝ * Real.sqrt ⟪y, D y⟫_ℝ := by
  have h := positive_form_cauchy_schwarz hD x y
  have hx := Real.sq_sqrt (hD.inner_nonneg_right x)
  have hy := Real.sq_sqrt (hD.inner_nonneg_right y)
  have hs : 0 ≤ Real.sqrt ⟪x, D x⟫_ℝ * Real.sqrt ⟪y, D y⟫_ℝ := by positivity
  have habs := sq_abs ⟪x, D y⟫_ℝ
  nlinarith

/-- A small positive form controls the Euclidean norm of its value by its
own directional energy. -/
theorem positive_form_norm_sq_le {D : E →L[ℝ] E} (hD : D.IsPositive)
    {epsilon : ℝ} (hbound : ∀ v, ⟪v, D v⟫_ℝ ≤ epsilon * ‖v‖ ^ 2) (w : E) :
    ‖D w‖ ^ 2 ≤ epsilon * ⟪w, D w⟫_ℝ := by
  have henergy := hD.inner_nonneg_right w
  have hcs := positive_form_cauchy_schwarz hD (D w) w
  rw [real_inner_self_eq_norm_sq] at hcs
  have hsmall := mul_le_mul_of_nonneg_right (hbound (D w)) henergy
  by_cases hzero : ‖D w‖ = 0
  · rw [hzero]
    have hDzero : D w = 0 := norm_eq_zero.mp hzero
    simp [hDzero]
  have hpos : 0 < ‖D w‖ ^ 2 := sq_pos_of_ne_zero hzero
  nlinarith

/-- The norm estimate in square-root form, as used for the patch field. -/
theorem positive_form_norm_le {D : E →L[ℝ] E} (hD : D.IsPositive)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hbound : ∀ v, ⟪v, D v⟫_ℝ ≤ epsilon * ‖v‖ ^ 2) (w : E) :
    ‖D w‖ ≤ Real.sqrt epsilon * Real.sqrt ⟪w, D w⟫_ℝ := by
  have h := positive_form_norm_sq_le hD hbound w
  have henergy := hD.inner_nonneg_right w
  have hroot : (Real.sqrt epsilon * Real.sqrt ⟪w, D w⟫_ℝ) ^ 2 =
      epsilon * ⟪w, D w⟫_ℝ := by
    rw [mul_pow, Real.sq_sqrt hepsilon, Real.sq_sqrt henergy]
  have hrootpos : 0 ≤ Real.sqrt epsilon * Real.sqrt ⟪w, D w⟫_ℝ := by positivity
  nlinarith [norm_nonneg (D w)]

end RegularPointCoordinates

end OAI
