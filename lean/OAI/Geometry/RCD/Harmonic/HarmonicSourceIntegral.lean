import OAI.Geometry.RCD.Sobolev.CutoffSourcePairing
import OAI.Geometry.RCD.Metric.CompactDensityTimeIntegral

namespace OAI

/-! # Integrating all three actual harmonic source components -/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace NNReal ENNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

private theorem integral_three_components {a b κ : ℝ} (hab : a ≤ b)
    (m c e ν : ℝ → ℝ)
    (hm : IntervalIntegrable m volume a b) (hc : IntervalIntegrable c volume a b)
    (he : IntervalIntegrable e volume a b)
    (hν : ∀ t ∈ Ioc a b, ν t = 2 * m t - 2 * κ * c t + e t) :
    (∫ t in a..b, ν t) =
      2 * (∫ t in a..b, m t) - 2 * κ * (∫ t in a..b, c t) + ∫ t in a..b, e t := by
  have hid : (∫ t in a..b, ν t) = ∫ t in a..b, (2 * m t - 2 * κ * c t + e t) := by
    apply intervalIntegral.integral_congr_ae
    exact Eventually.of_forall fun t ht => hν t (by simpa only [uIoc_of_le hab] using ht)
  rw [hid, intervalIntegral.integral_add ((hm.const_mul 2).sub (hc.const_mul (2 * κ))) he,
    intervalIntegral.integral_sub (hm.const_mul 2) (hc.const_mul (2 * κ)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
  {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0} {v : E}
  (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
  {ρ C : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ C)

omit [ProperSpace X] [FiniteDimensional ℝ E] [μ.Regular] [IsLocallyFiniteMeasure μ] in
private theorem curvature_integrable :
    Integrable (fun z => χ.weight z * localGamma μ hQ (U v) (U v) z) μ := by
  exact (localGamma_memL1 μ hQ (U v) (U v)).bdd_mul
    χ.weight.continuous.aestronglyMeasurable (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (χ.bounds z).1]
      exact (χ.bounds z).2)

omit [ProperSpace X] [FiniteDimensional ℝ E] [μ.Regular] [IsLocallyFiniteMeasure μ] in
private theorem curvature_zero_off : ∀ᵐ z ∂μ, z ∉ closedBall p (2 * ρ) →
    χ.weight z * localGamma μ hQ (U v) (U v) z = 0 := by
  filter_upwards with z hz
  rw [χ.zero z (by simpa only [mem_closedBall, dist_comm, not_le] using hz), zero_mul]

include hk in
/-- The short-time full signed source has exactly the three integrals
that have been bounded separately. Each integral is justified in L1. -/
theorem LocalHarmonicEnergy.integrated_average_source_components
    (A : Set X) (hA : MeasurableSet A) (hbounded : Bornology.IsBounded A)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ t in (0 : ℝ)..s, (∫ᵛ z, kernelAverage μ ker t A z
      ∂<•(G.cutoffSource μ hQ χ.weight χ.sobolev χ.laplacian))) =
      2 * (∫ t in (0 : ℝ)..s, ⟪v, cutoffAverageHeatMassAt μ hQ hk χ.weight.continuous
        (χ.hasCompactSupport μ hQ) M A hA hbounded t v⟫_ℝ) -
      2 * κ * (∫ t in (0 : ℝ)..s, ∫ z, kernelAverage μ ker t A z *
        (χ.weight z * localGamma μ hQ (U v) (U v) z) ∂μ) +
      ∫ t in (0 : ℝ)..s, ∫ z, kernelAverage μ ker t A z *
        cutoffSourceDensity μ hQ G.energy χ.sobolev χ.laplacian z ∂μ := by
  apply integral_three_components hs
  · exact cutoffAverageHeatMassAt_intervalIntegrable_zero μ hQ hk χ.weight.continuous
      (χ.hasCompactSupport μ hQ) M χ.bounds A hA hbounded v hs
  · exact average_density_intervalIntegrable_zero μ hQ hk A hA hbounded.measure_lt_top.ne
      (curvature_integrable μ hQ χ) (isCompact_closedBall p (2 * ρ)) (curvature_zero_off μ hQ χ) hs
  · exact average_density_intervalIntegrable_zero μ hQ hk A hA hbounded.measure_lt_top.ne
      (cutoffSourceDensity_integrable μ hQ _ _ _) (isCompact_closedBall p (2 * ρ))
      (χ.error_zero_off_outerBall μ hQ G.energy) hs
  · intro t ht
    exact G.average_source_components μ hQ hk χ ht.1 A hA hbounded

include hk in
/-- Above the averaging scale, integration preserves the cancellation
between the average and point source in every component. -/
theorem LocalHarmonicEnergy.integrated_difference_source_components (hρ : 0 < ρ)
    (A : Set X) (hA : MeasurableSet A) (hbounded : Bornology.IsBounded A) (x : X)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    (∫ τ in s..t,
      (∫ᵛ z, kernelAverage μ ker τ A z ∂<•(G.cutoffSource μ hQ χ.weight χ.sobolev χ.laplacian)) -
      (∫ᵛ z, ker τ x z ∂<•(G.cutoffSource μ hQ χ.weight χ.sobolev χ.laplacian))) =
      2 * (∫ τ in s..t, ⟪v, (cutoffAverageHeatMassAt μ hQ hk χ.weight.continuous
        (χ.hasCompactSupport μ hQ) M A hA hbounded τ -
        cutoffHeatMassAt μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ) M τ x) v⟫_ℝ) -
      2 * κ * (∫ τ in s..t, ∫ z, (kernelAverage μ ker τ A z - ker τ x z) *
        (χ.weight z * localGamma μ hQ (U v) (U v) z) ∂μ) +
      ∫ τ in s..t, ∫ z, (kernelAverage μ ker τ A z - ker τ x z) *
        cutoffSourceDensity μ hQ G.energy χ.sobolev χ.laplacian z ∂μ := by
  apply integral_three_components hst
  · exact cutoffAverageHeatMassAt_difference_intervalIntegrable μ hQ hk χ.weight.continuous
      (χ.hasCompactSupport μ hQ) M A hA hbounded x v hs hst
  · exact difference_density_intervalIntegrable μ hQ hk A hA hbounded x
      (curvature_integrable μ hQ χ) (isCompact_closedBall p (2 * ρ)) (curvature_zero_off μ hQ χ) hs hst
  · exact difference_density_intervalIntegrable μ hQ hk A hA hbounded x
      (cutoffSourceDensity_integrable μ hQ _ _ _) (isCompact_closedBall p (2 * ρ))
      (χ.error_zero_off_outerBall μ hQ G.energy) hs hst
  · intro τ hτ
    exact G.difference_source_components μ hQ hk χ hρ (hs.trans hτ.1) A hA hbounded x

end RegularPointCoordinates

end

end OAI
