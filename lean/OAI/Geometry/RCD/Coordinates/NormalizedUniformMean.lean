import OAI.Geometry.RCD.Coordinates.NormalizedUniformL2

namespace OAI

/-! # Normalized integral convergence under varying finite measures -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem normalized_mean_tendsto_zero (μ : ℕ → Measure X)
    [∀ k, IsFiniteMeasure (μ k)] (hmass : ∀ k, 0<(μ k).real univ)
    (f : ℕ → X → ℝ)
    (hlim : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ᵐ x ∂μ k, |f k x|≤η) :
    Tendsto (fun k => ((μ k).real univ)⁻¹*(∫ x, f k x ∂μ k)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  filter_upwards [hlim (η/2) (half_pos hη)] with k hk
  have hi := norm_integral_le_of_norm_le_const (μ := μ k) (f := f k) (C := η/2)
    (hk.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)
  have hb := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (hmass k).le)
  rw [mul_comm (η/2),← mul_assoc,inv_mul_cancel₀ (hmass k).ne',one_mul] at hb
  rw [Real.dist_eq,sub_zero,abs_mul,abs_of_nonneg (inv_nonneg.mpr (hmass k).le)]
  have hb' : ((μ k).real univ)⁻¹*|∫ x, f k x ∂μ k|≤η/2 := by
    simpa only [Real.norm_eq_abs] using hb
  exact hb'.trans_lt (half_lt_self hη)

end RegularPointCoordinates

end

end OAI
