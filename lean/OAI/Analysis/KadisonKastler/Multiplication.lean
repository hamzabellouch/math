import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Multiplicative defects of maps close to a representation

These estimates are the normed-algebra calculation used in the UCP criterion
in §2 of *Universal strong Kadison–Kastler stability* (2026). They require no
positivity theorem: contractivity, where used, is an explicit hypothesis.
-/

namespace KadisonKastler

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A]
  [NormedRing B] [NormedAlgebra ℂ B]

/-- A map within `e` of an isometric representation has norm at most `1 + e`. -/
theorem norm_image_le_of_close_to_isometric_hom
    (ρ : A →ₐ[ℂ] B) (F : A →ₗ[ℂ] B) {e : ℝ}
    (hρ : ∀ x, ‖ρ x‖ = ‖x‖)
    (hclose : ∀ x, ‖F x - ρ x‖ ≤ e * ‖x‖) (x : A) :
    ‖F x‖ ≤ (1 + e) * ‖x‖ := by
  calc
    ‖F x‖ ≤ ‖F x - ρ x‖ + ‖ρ x‖ := norm_le_norm_sub_add _ _
    _ ≤ e * ‖x‖ + ‖x‖ := by rw [hρ]; exact add_le_add (hclose x) le_rfl
    _ = (1 + e) * ‖x‖ := by ring

/-- A three-term defect estimate, keeping the norm of the map on the left
factor visible so that contractivity can improve the final bound. -/
theorem multiplicative_defect_le_three_terms
    (ρ : A →ₐ[ℂ] B) (F : A →ₗ[ℂ] B) {e : ℝ}
    (hρ : ∀ x, ‖ρ x‖ = ‖x‖)
    (hclose : ∀ x, ‖F x - ρ x‖ ≤ e * ‖x‖) (x y : A) :
    ‖F (x * y) - F x * F y‖ ≤
      e * ‖x * y‖ + e * ‖x‖ * ‖y‖ + ‖F x‖ * (e * ‖y‖) := by
  have hreverse (z : A) : ‖ρ z - F z‖ ≤ e * ‖z‖ := by
    simpa only [norm_sub_rev] using hclose z
  have hexpand : F (x * y) - F x * F y =
      (F (x * y) - ρ (x * y)) + (ρ x - F x) * ρ y + F x * (ρ y - F y) := by
    have hmul : ρ (x * y) = ρ x * ρ y := map_mul ρ x y
    rw [hmul]
    noncomm_ring
  rw [hexpand]
  calc
    ‖F (x * y) - ρ (x * y) + (ρ x - F x) * ρ y + F x * (ρ y - F y)‖ ≤
        ‖F (x * y) - ρ (x * y)‖ + ‖(ρ x - F x) * ρ y‖ +
          ‖F x * (ρ y - F y)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ e * ‖x * y‖ + e * ‖x‖ * ‖y‖ + ‖F x‖ * (e * ‖y‖) := by
      apply add_le_add
      · apply add_le_add (hclose (x * y))
        calc
          ‖(ρ x - F x) * ρ y‖ ≤ ‖ρ x - F x‖ * ‖ρ y‖ := norm_mul_le _ _
          _ ≤ e * ‖x‖ * ‖y‖ := by
            rw [hρ]
            exact mul_le_mul_of_nonneg_right (hreverse x) (norm_nonneg _)
      · exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_left (hreverse y) (norm_nonneg _))

/-- The general perturbation bound without an assumption that `F` is contractive. -/
theorem multiplicative_defect_le_of_close_to_isometric_hom
    (ρ : A →ₐ[ℂ] B) (F : A →ₗ[ℂ] B) {e : ℝ} (he : 0 ≤ e)
    (hρ : ∀ x, ‖ρ x‖ = ‖x‖)
    (hclose : ∀ x, ‖F x - ρ x‖ ≤ e * ‖x‖) (x y : A) :
    ‖F (x * y) - F x * F y‖ ≤ (3 * e + e ^ 2) * ‖x‖ * ‖y‖ := by
  calc
    ‖F (x * y) - F x * F y‖ ≤
        e * ‖x * y‖ + e * ‖x‖ * ‖y‖ + ‖F x‖ * (e * ‖y‖) :=
      multiplicative_defect_le_three_terms ρ F hρ hclose x y
    _ ≤ e * (‖x‖ * ‖y‖) + e * ‖x‖ * ‖y‖ + ((1 + e) * ‖x‖) * (e * ‖y‖) := by
      apply add_le_add
      · exact add_le_add (mul_le_mul_of_nonneg_left (norm_mul_le x y) he) le_rfl
      · exact mul_le_mul_of_nonneg_right
          (norm_image_le_of_close_to_isometric_hom ρ F hρ hclose x)
          (mul_nonneg he (norm_nonneg y))
    _ = (3 * e + e ^ 2) * ‖x‖ * ‖y‖ := by ring

/-- Contractivity removes the quadratic term, yielding the `3e` estimate
used for UCP maps in the manuscript. -/
theorem multiplicative_defect_le_of_contractive_close_to_isometric_hom
    (ρ : A →ₐ[ℂ] B) (F : A →ₗ[ℂ] B) {e : ℝ} (he : 0 ≤ e)
    (hρ : ∀ x, ‖ρ x‖ = ‖x‖)
    (hclose : ∀ x, ‖F x - ρ x‖ ≤ e * ‖x‖)
    (hcontractive : ∀ x, ‖F x‖ ≤ ‖x‖) (x y : A) :
    ‖F (x * y) - F x * F y‖ ≤ 3 * e * ‖x‖ * ‖y‖ := by
  calc
    ‖F (x * y) - F x * F y‖ ≤
        e * ‖x * y‖ + e * ‖x‖ * ‖y‖ + ‖F x‖ * (e * ‖y‖) :=
      multiplicative_defect_le_three_terms ρ F hρ hclose x y
    _ ≤ e * (‖x‖ * ‖y‖) + e * ‖x‖ * ‖y‖ + ‖x‖ * (e * ‖y‖) := by
      apply add_le_add
      · exact add_le_add (mul_le_mul_of_nonneg_left (norm_mul_le x y) he) le_rfl
      · exact mul_le_mul_of_nonneg_right (hcontractive x) (mul_nonneg he (norm_nonneg y))
    _ = 3 * e * ‖x‖ * ‖y‖ := by ring

end KadisonKastler

end OAI
