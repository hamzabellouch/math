import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # L² gradient pairings for a bounded-gradient factor -/

open Set Filter MeasureTheory
open scoped NNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem localGamma_memLp_of_bounded_gradient (f g : SobolevSpace μ hQ) (L : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ f x ≤ L) :
    MemLp (localGamma μ hQ f g) 2 μ := by
  apply ((Lp.memLp (SobolevSpace.minimalSlope μ hQ g)).const_mul (L : ℝ)).mono'
    (localGamma_memL1 μ hQ f g).aestronglyMeasurable
  filter_upwards [hf, localGamma_abs_le μ hQ f g,
    (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ g)] with x hx hΓ hg
  rw [Real.norm_eq_abs]
  exact hΓ.trans (mul_le_mul_of_nonneg_right hx hg)

omit [ProperSpace X] in
theorem weightedGamma_eq_L2_inner (f g : SobolevSpace μ hQ)
    (hΓ : MemLp (localGamma μ hQ f g) 2 μ) (w : Lp ℝ 2 μ) :
    weightedGamma μ hQ w f g = inner ℝ w (hΓ.toLp (localGamma μ hQ f g)) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hΓ.coeFn_toLp] with x hx
  simp only [Real.inner_apply, hx]

variable [μ.Regular]

theorem weightedGamma_heat_tendsto (f g : SobolevSpace μ hQ)
    (hΓ : MemLp (localGamma μ hQ f g) 2 μ) (w : Lp ℝ 2 μ) :
    Tendsto (fun s => weightedGamma μ hQ (heatAt μ hQ s w) f g) (𝓝 0)
      (𝓝 (weightedGamma μ hQ w f g)) := by
  simp only [weightedGamma_eq_L2_inner μ hQ f g hΓ]
  have h : Tendsto (fun s => inner ℝ (heatAt μ hQ s w)
      (hΓ.toLp (localGamma μ hQ f g))) (𝓝 0)
      (𝓝 (inner ℝ (heatAt μ hQ 0 w) (hΓ.toLp (localGamma μ hQ f g)))) :=
    ((heatAt_continuous μ hQ w).tendsto 0).inner tendsto_const_nhds
  simpa only [heatAt_zero, one_apply_eq_self] using h

end RegularPointCoordinates

end

end OAI
