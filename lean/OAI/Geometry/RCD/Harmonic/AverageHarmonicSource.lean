import OAI.Geometry.RCD.Heat.HarmonicBochnerHeatSource
import OAI.Geometry.RCD.Metric.AverageMassEnvelope
import OAI.Geometry.RCD.Heat.AveragedHeatSource

namespace OAI

/-! # Averaging the full harmonic cutoff source -/

open Set Metric MeasureTheory
open scoped NNReal InnerProductSpace BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

/-- The averaged kernel is globally bounded by reciprocal testing volume.
This makes it a legitimate test for a finite signed source, even at
singular source poles. -/
def boundedKernelAverage {t : ℝ} (ht : 0 < t) (A : Set X)
    (hA : MeasurableSet A) (hbounded : Bornology.IsBounded A) : X →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (kernelAverage μ ker t A)
    (kernelAverage_continuous μ hQ hk ht hA hbounded) (μ.real A)⁻¹
    (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (kernelAverage_bounds μ hQ hk ht A z).1]
                 exact (kernelAverage_bounds μ hQ hk ht A z).2)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
  {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0} {v : E}

/-- Exact mass, curvature and cutoff-density decomposition of the actual
averaged signed source. No absolute-continuity replacement of M is made. -/
theorem LocalHarmonicEnergy.average_cutoffSource
    (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (χ : X →ᵇ ℝ) (hcompact : HasCompactSupport (χ : X → ℝ))
    (c : SobolevSpace μ hQ) (q : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t)
    (A : Set X) (hA : MeasurableSet A) (hbounded : Bornology.IsBounded A) :
    (∫ᵛ z, kernelAverage μ ker t A z ∂<•(G.cutoffSource μ hQ χ c q)) =
      2 * ⟪v, cutoffAverageHeatMass μ hQ hk χ.continuous hcompact M ht A hA hbounded v⟫_ℝ -
      2 * κ * (∫ z, χ z * kernelAverage μ ker t A z * localGamma μ hQ (U v) (U v) z ∂μ) +
      ∫ z, kernelAverage μ ker t A z * cutoffSourceDensity μ hQ G.energy c q z ∂μ := by
  let w := boundedKernelAverage μ hQ hk ht A hA hbounded
  have hM : M.weightedOperator (w * χ) =
      cutoffAverageHeatMass μ hQ hk χ.continuous hcompact M ht A hA hbounded := by
    unfold cutoffAverageHeatMass
    congr 1
    ext z
    change kernelAverage μ ker t A z * χ z = χ z * kernelAverage μ ker t A z
    ring
  have hG : (∫ z, (w * χ) z * localGamma μ hQ (U v) (U v) z ∂μ) =
      ∫ z, χ z * kernelAverage μ ker t A z * localGamma μ hQ (U v) (U v) z ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      change (kernelAverage μ ker t A z * χ z) * _ = _
      ring
  have he := G.integral_cutoffSource μ hQ χ w c q
  rw [hM, hG] at he
  exact he

end RegularPointCoordinates

end

end OAI
