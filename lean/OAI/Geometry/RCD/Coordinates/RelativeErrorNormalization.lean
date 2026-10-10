import OAI.Geometry.RCD.Harmonic.ProjectionFailureSequence

namespace OAI

/-! # Normalizing only after the outer residual bound -/

open Filter
open scoped Topology

noncomputable section
namespace RegularPointCoordinates

theorem normalized_relative_bound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (x : H) {α s C : ℝ} (hα : 0 < α) (hx : ‖x‖ ≤ C * (α + s)) :
    ‖α⁻¹ • x‖ ≤ C * (1 + s / α) := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hα]
  apply (mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hα.le)).trans_eq
  field_simp

/-- Dividing the already proved unnormalized outer bound gives a
uniform bound on every sufficiently late normalized residual. -/
theorem normalized_relative_eventually_bounded
    {H : ℕ → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedSpace ℝ (H i)]
    (x : ∀ i, H i) {α s : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hα : ∀ i, 0 < α i) (hx : ∀ i, ‖x i‖ ≤ C * (α i + s i))
    (hratio : Tendsto (fun i => s i / α i) atTop (𝓝 0)) :
    ∀ᶠ i in atTop, ‖(α i)⁻¹ • x i‖ ≤ 2 * C := by
  filter_upwards [hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with i hi
  have hb := normalized_relative_bound (x i) (hα i) (hx i)
  nlinarith only [hb, mul_nonneg hC (le_of_lt (sub_pos.mpr hi))]

/-- The normalized forcing tends to zero when its original size is
linear in a source error negligible relative to the residual. -/
theorem normalized_source_error_tendsto_zero
    {H : ℕ → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedSpace ℝ (H i)]
    (e : ∀ i, H i) {α s : ℕ → ℝ} {C : ℝ}
    (hα : ∀ i, 0 < α i) (he : ∀ i, ‖e i‖ ≤ C * s i)
    (hratio : Tendsto (fun i => s i / α i) atTop (𝓝 0)) :
    Tendsto (fun i => ‖(α i)⁻¹ • e i‖) atTop (𝓝 0) := by
  have hb (i : ℕ) : ‖(α i)⁻¹ • e i‖ ≤ C * (s i / α i) := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hα i)]
    apply (mul_le_mul_of_nonneg_left (he i) (inv_nonneg.mpr (hα i).le)).trans_eq
    ring
  exact squeeze_zero (fun i => norm_nonneg _) hb
    (by simpa only [mul_zero] using tendsto_const_nhds.mul hratio)

end RegularPointCoordinates

end

end OAI
