import OAI.Geometry.RCD.Coordinates.NormalizedUniformMean

namespace OAI

/-! # Vanishing value errors against uniformly bounded rescaled factors -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem normalized_product_error_tendsto (μ : ℕ → Measure X)
    [∀ k, IsFiniteMeasure (μ k)] (hmass : ∀ k, 0<(μ k).real univ)
    (z b : ℕ → X → ℝ) {C : ℝ} (hC : 0≤C)
    (hb : ∀ᶠ k in atTop, ∀ᵐ x ∂μ k, |b k x|≤C)
    (hz : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ᵐ x ∂μ k, |z k x|≤δ) :
    Tendsto (fun k => ((μ k).real univ)⁻¹*(∫ x, z k x*b k x ∂μ k)) atTop (𝓝 0) := by
  apply normalized_mean_tendsto_zero μ hmass
  intro δ hδ
  have hden : 0<C+1 := by linarith
  filter_upwards [hb,hz (δ/(C+1)) (div_pos hδ hden)] with k hbk hzk
  filter_upwards [hbk,hzk] with x hbx hzx
  rw [abs_mul]
  have hh := mul_le_mul hzx hbx (abs_nonneg (b k x)) (div_nonneg hδ.le hden.le)
  have hsmall : δ/(C+1)*C≤δ := by
    have hd := (div_mul_cancel₀ δ hden.ne')
    have hp := mul_nonneg (div_nonneg hδ.le hden.le) (show (0:ℝ)≤1 by norm_num)
    nlinarith
  exact hh.trans hsmall

end RegularPointCoordinates

end

end OAI
