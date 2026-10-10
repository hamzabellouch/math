import OAI.Geometry.RCD.Sobolev.AveragedCutoffError
import OAI.Geometry.RCD.Metric.AverageMassInitial

namespace OAI

/-! # The full source difference in the actual three components -/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
  {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0} {v : E}
  (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
  {ρ C : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ C)

include hk in
/-- The full averaged source is the positive mass, curvature density,
and actual product-rule error, with compatible representatives. -/
theorem LocalHarmonicEnergy.average_source_components
    {t : ℝ} (ht : 0 < t) (A : Set X) (hA : MeasurableSet A)
    (hbounded : Bornology.IsBounded A) :
    (∫ᵛ z, kernelAverage μ ker t A z ∂<•(G.cutoffSource μ hQ χ.weight χ.sobolev χ.laplacian)) =
      2 * ⟪v, cutoffAverageHeatMassAt μ hQ hk χ.weight.continuous
        (χ.hasCompactSupport μ hQ) M A hA hbounded t v⟫_ℝ -
      2 * κ * (∫ z, kernelAverage μ ker t A z *
        (χ.weight z * localGamma μ hQ (U v) (U v) z) ∂μ) +
      ∫ z, kernelAverage μ ker t A z *
        cutoffSourceDensity μ hQ G.energy χ.sobolev χ.laplacian z ∂μ := by
  rw [cutoffAverageHeatMassAt_of_pos μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ) M A hA hbounded ht]
  rw [G.average_cutoffSource μ hQ hk χ.weight (χ.hasCompactSupport μ hQ) χ.sobolev χ.laplacian ht A hA hbounded]
  congr 2
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by ring

include hk in
/-- Subtracting the pointwise source preserves the full positive-measure
term and gives the kernel difference against each absolutely continuous term. -/
theorem LocalHarmonicEnergy.difference_source_components (hρ : 0 < ρ)
    {t : ℝ} (ht : 0 < t) (A : Set X) (hA : MeasurableSet A)
    (hbounded : Bornology.IsBounded A) (x : X) :
    (∫ᵛ z, kernelAverage μ ker t A z ∂<•(G.cutoffSource μ hQ χ.weight χ.sobolev χ.laplacian)) -
      (∫ᵛ z, ker t x z ∂<•(G.cutoffSource μ hQ χ.weight χ.sobolev χ.laplacian)) =
      2 * ⟪v, (cutoffAverageHeatMassAt μ hQ hk χ.weight.continuous
        (χ.hasCompactSupport μ hQ) M A hA hbounded t -
        cutoffHeatMassAt μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ) M t x) v⟫_ℝ -
      2 * κ * (∫ z, (kernelAverage μ ker t A z - ker t x z) *
        (χ.weight z * localGamma μ hQ (U v) (U v) z) ∂μ) +
      ∫ z, (kernelAverage μ ker t A z - ker t x z) *
        cutoffSourceDensity μ hQ G.energy χ.sobolev χ.laplacian z ∂μ := by
  let c := fun z => χ.weight z * localGamma μ hQ (U v) (U v) z
  let d := cutoffSourceDensity μ hQ G.energy χ.sobolev χ.laplacian
  have hc : Integrable c μ := (localGamma_memL1 μ hQ (U v) (U v)).bdd_mul
    χ.weight.continuous.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (χ.bounds z).1]
      exact (χ.bounds z).2)
  have hczero : ∀ᵐ z ∂μ, z ∉ closedBall p (2 * ρ) → c z = 0 := by
    filter_upwards with z hz
    have hχ := χ.zero z (by simpa only [mem_closedBall, dist_comm, not_le] using hz)
    simp only [c, hχ, zero_mul]
  have hd : Integrable d μ := cutoffSourceDensity_integrable μ hQ _ _ _
  have hdzero := χ.error_zero_off_outerBall μ hQ G.energy
  have hsub (f : X → ℝ) (hf : Integrable f μ)
      (hz : ∀ᵐ z ∂μ, z ∉ closedBall p (2 * ρ) → f z = 0) :
      (∫ z, (kernelAverage μ ker t A z - ker t x z) * f z ∂μ) =
        (∫ z, kernelAverage μ ker t A z * f z ∂μ) - ∫ z, ker t x z * f z ∂μ := by
    simp_rw [sub_mul]
    exact integral_sub
      (continuous_mul_integrable_compact μ (kernelAverage_continuous μ hQ hk ht hA hbounded)
        hf (isCompact_closedBall p (2 * ρ)) hz)
      (continuous_mul_integrable_compact μ (hk.continuous_right t ht x)
        hf (isCompact_closedBall p (2 * ρ)) hz)
  have hqzero : ∀ᵐ z ∂μ, z ∉ closedBall p (2 * ρ) → χ.laplacian z = 0 := by
    filter_upwards [χ.laplacian_locality] with z hz hn
    exact hz (Or.inr (by simpa only [mem_closedBall, dist_comm, not_le] using hn))
  have hp := G.kernel_cutoffSource μ hQ hk χ.weight (χ.hasCompactSupport μ hQ)
    χ.sobolev χ.representative χ.laplacian p (mul_pos (by norm_num) hρ)
    (fun z hz => χ.zero z (by simpa only [mem_closedBall, dist_comm, not_le] using hz)) hqzero ht x
  have hg : ⟪v, cutoffHeatGram μ hQ hk χ.weight.continuous
      (χ.hasCompactSupport μ hQ) U ht x 0 v⟫_ℝ = ∫ z, ker t x z * c z ∂μ := by
    rw [cutoffHeatGram_energy]
    simp only [zero_mul, add_zero]
    apply integral_congr_ae
    filter_upwards [localGamma_self μ hQ (U v)] with z hz
    dsimp only [c]
    rw [hz]
    ring
  rw [hg] at hp
  rw [G.average_source_components μ hQ hk χ ht A hA hbounded, hp,
    cutoffHeatMassAt_of_pos μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ) M ht,
    sub_apply, inner_sub_right, hsub c hc hczero, hsub d hd hdzero]
  ring

end RegularPointCoordinates

end

end OAI
