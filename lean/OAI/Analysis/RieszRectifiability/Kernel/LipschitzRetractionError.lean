import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Topology
open scoped NNReal

theorem lipschitz_retraction_error_integral_bound {d q k : ℕ}
    (μ : Measure (Ambient d)) (v : Ambient d → Ambient q) (J : ℝ≥0)
    (hv : LipschitzWith J v) (P : Ambient d → Ambient d) (hP : Measurable P)
    (δ : ℝ) (hδ : 0 ≤ δ) (r : Ambient d → Ambient k)
    (hr : Integrable (fun x => ‖r x‖ ^ 2) μ)
    (hbound : ∀ᵐ x ∂μ, dist x (P x) ≤ δ * ‖r x‖) :
    Integrable (fun x => ‖v x - v (P x)‖ ^ 2) μ ∧
      (∫ x, ‖v x - v (P x)‖ ^ 2 ∂μ) ≤ ((J : ℝ) * δ) ^ 2 * (∫ x, ‖r x‖ ^ 2 ∂μ) := by
  have hb : ∀ᵐ x ∂μ, ‖v x - v (P x)‖ ^ 2 ≤ ((J : ℝ) * δ) ^ 2 * ‖r x‖ ^ 2 := by
    filter_upwards [hbound] with x hx
    have hn : ‖v x - v (P x)‖ ≤ ((J : ℝ) * δ) * ‖r x‖ := by
      calc
        _ = dist (v x) (v (P x)) := (dist_eq_norm _ _).symm
        _ ≤ (J : ℝ) * dist x (P x) := hv.dist_le_mul x (P x)
        _ ≤ (J : ℝ) * (δ * ‖r x‖) := mul_le_mul_of_nonneg_left hx J.coe_nonneg
        _ = _ := (mul_assoc _ _ _).symm
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (mul_nonneg J.coe_nonneg hδ) (norm_nonneg _))).mpr hn
    simpa only [mul_pow] using! hs
  have hm : AEStronglyMeasurable (fun x => ‖v x - v (P x)‖ ^ 2) μ :=
    ((hv.continuous.measurable.sub (hv.continuous.measurable.comp hP)).norm.pow_const 2).aestronglyMeasurable
  have hi := (hr.const_mul (((J : ℝ) * δ) ^ 2)).mono' hm (hb.mono fun x hx => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖v x - v (P x)‖)]
    exact hx)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, ((J : ℝ) * δ) ^ 2 * ‖r x‖ ^ 2 ∂μ :=
      integral_mono_ae hi (hr.const_mul _) hb
    _ = _ := integral_const_mul _ _

theorem lipschitz_retraction_error_tendsto_zero {d q k : ℕ}
    (μ : ℕ → Measure (Ambient d)) (v : Ambient d → Ambient q) (J : ℝ≥0)
    (hv : LipschitzWith J v) (P : ℕ → Ambient d → Ambient d) (hP : ∀ j, Measurable (P j))
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 ≤ δ j) (hδlim : Tendsto δ atTop (𝓝 0))
    (r : ℕ → Ambient d → Ambient k) (hr : ∀ j, Integrable (fun x => ‖r j x‖ ^ 2) (μ j))
    (hbound : ∀ j, ∀ᵐ x ∂μ j, dist x (P j x) ≤ δ j * ‖r j x‖)
    (B : ℝ) (hB : ∀ j, (∫ x, ‖r j x‖ ^ 2 ∂μ j) ≤ B) :
    Tendsto (fun j => ∫ x, ‖v x - v (P j x)‖ ^ 2 ∂μ j) atTop (𝓝 0) := by
  have hlim : Tendsto (fun j => ((J : ℝ) * δ j) ^ 2 * B) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] using!
      ((hδlim.const_mul (J : ℝ)).pow 2).mul_const B
  apply squeeze_zero (fun j => integral_nonneg fun x => sq_nonneg ‖v x - v (P j x)‖) _ hlim
  intro j
  exact (lipschitz_retraction_error_integral_bound (μ j) v J hv (P j) (hP j)
    (δ j) (hδ j) (r j) (hr j) (hbound j)).2.trans
    (mul_le_mul_of_nonneg_left (hB j) (sq_nonneg _))

end

end RieszRectifiability

end OAI
