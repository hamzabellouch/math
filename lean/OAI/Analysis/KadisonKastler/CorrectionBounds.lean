import OAI.Analysis.KadisonKastler.Transport
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Bounds for correcting a transported multiplication

These are the inverse and composition estimates used in the UCP criterion
of §2 of *Universal strong Kadison–Kastler stability* (2026). The estimates are formulated for an explicitly supplied correction map.
-/

namespace KadisonKastler

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The inverse norm estimate for a linear equivalence within `η < 1`
of the identity. -/
theorem norm_inverse_le_of_close_to_id (L : E ≃ₗ[ℂ] E) {η : ℝ} (hη : η < 1)
    (hclose : ∀ x, ‖L x - x‖ ≤ η * ‖x‖) (x : E) :
    ‖L.symm x‖ ≤ (1 - η)⁻¹ * ‖x‖ := by
  have hpos : 0 < 1 - η := sub_pos.mpr hη
  apply (le_inv_mul_iff₀ hpos).mpr
  have hnorm := norm_le_norm_sub_add (L.symm x) x
  have herror := hclose (L.symm x)
  rw [L.apply_symm_apply, norm_sub_rev] at herror
  linarith

/-- The inverse displacement estimate corresponding to a near-identity
linear equivalence. -/
theorem norm_inverse_sub_le_of_close_to_id (L : E ≃ₗ[ℂ] E) {η : ℝ}
    (hη₀ : 0 ≤ η) (hη : η < 1) (hclose : ∀ x, ‖L x - x‖ ≤ η * ‖x‖)
    (x : E) : ‖L.symm x - x‖ ≤ (η / (1 - η)) * ‖x‖ := by
  have herror := hclose (L.symm x)
  rw [L.apply_symm_apply, norm_sub_rev] at herror
  calc
    ‖L.symm x - x‖ ≤ η * ‖L.symm x‖ := herror
    _ ≤ η * ((1 - η)⁻¹ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_inverse_le_of_close_to_id L hη hclose x) hη₀
    _ = (η / (1 - η)) * ‖x‖ := by rw [div_eq_mul_inv, mul_assoc]

/-- Composing a contraction with an inverse correction adds at most the
inverse displacement to the original comparison error. -/
theorem norm_correctedMap_sub_le (L : E ≃ₗ[ℂ] E) (F ρ : E →ₗ[ℂ] G)
    {η e : ℝ} (hη₀ : 0 ≤ η) (hη : η < 1)
    (hL : ∀ x, ‖L x - x‖ ≤ η * ‖x‖)
    (hF : ∀ x, ‖F x‖ ≤ ‖x‖) (hclose : ∀ x, ‖F x - ρ x‖ ≤ e * ‖x‖)
    (x : E) : ‖F (L.symm x) - ρ x‖ ≤ (e + η / (1 - η)) * ‖x‖ := by
  calc
    ‖F (L.symm x) - ρ x‖ ≤ ‖F (L.symm x) - F x‖ + ‖F x - ρ x‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖L.symm x - x‖ + e * ‖x‖ := by
      apply add_le_add _ (hclose x)
      simpa only [map_sub] using hF (L.symm x - x)
    _ ≤ (η / (1 - η)) * ‖x‖ + e * ‖x‖ :=
      add_le_add (norm_inverse_sub_le_of_close_to_id L hη₀ hη hL x) le_rfl
    _ = (e + η / (1 - η)) * ‖x‖ := by ring

/-- The correction parameter furnished by the multiplication estimate is
small enough for inversion at the manuscript's UCP tolerance. -/
theorem ucp_correction_parameter_bounds {e : ℝ} (he : 0 ≤ e) (he₁ : e < 1 / 1000) :
    0 ≤ 30 * e / (1 - e) ∧ 30 * e / (1 - e) < 1 := by
  have hden : 0 < 1 - e := by linarith
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) he) hden.le
  · apply (div_lt_one hden).mpr
    linarith

/-- The numerical estimate in the UCP criterion:
`e + η / (1 - η) ≤ 32e` for `η = 30e / (1 - e)`. -/
theorem ucp_correction_constant_le {e : ℝ} (he : 0 ≤ e) (he₁ : e < 1 / 1000) :
    e + (30 * e / (1 - e)) / (1 - 30 * e / (1 - e)) ≤ 32 * e := by
  have hden : 0 < 1 - e := by linarith
  have hden₃₁ : 0 < 1 - 31 * e := by linarith
  have hη := (ucp_correction_parameter_bounds he he₁).2
  have hdenη : 0 < 1 - 30 * e / (1 - e) := sub_pos.mpr hη
  have hid : (30 * e / (1 - e)) / (1 - 30 * e / (1 - e)) =
      30 * e / (1 - 31 * e) := by
    field_simp [hden.ne', hden₃₁.ne', hdenη.ne']
    ring
  rw [hid]
  have hbound : 30 * e / (1 - 31 * e) ≤ 31 * e := by
    apply (div_le_iff₀ hden₃₁).mpr
    have hproduct : 0 ≤ e * (1 - 961 * e) :=
      mul_nonneg he (by linarith)
    nlinarith
  linarith

/-- The corrected map is within `32e` of the comparison map under the
explicit correction bound appearing in the UCP criterion. -/
theorem norm_correctedMap_sub_le_thirty_two_mul
    (L : E ≃ₗ[ℂ] E) (F ρ : E →ₗ[ℂ] G) {e : ℝ}
    (he : 0 ≤ e) (he₁ : e < 1 / 1000)
    (hL : ∀ x, ‖L x - x‖ ≤ (30 * e / (1 - e)) * ‖x‖)
    (hF : ∀ x, ‖F x‖ ≤ ‖x‖) (hclose : ∀ x, ‖F x - ρ x‖ ≤ e * ‖x‖)
    (x : E) : ‖F (L.symm x) - ρ x‖ ≤ (32 * e) * ‖x‖ := by
  obtain ⟨hη₀, hη⟩ := ucp_correction_parameter_bounds he he₁
  exact (norm_correctedMap_sub_le L F ρ hη₀ hη hL hF hclose x).trans
    (mul_le_mul_of_nonneg_right (ucp_correction_constant_le he he₁) (norm_nonneg x))

end KadisonKastler

end OAI
