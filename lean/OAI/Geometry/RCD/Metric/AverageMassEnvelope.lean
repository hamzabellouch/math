import OAI.Geometry.RCD.Heat.GaussianIntegralEnvelope
import OAI.Geometry.RCD.Heat.KernelMeasureBounds

namespace OAI

/-! # Shell estimates for the actual averaged Bochner heat mass -/

open Set Metric MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {χ : X → ℝ} (hχ : Continuous χ) (hsχ : HasCompactSupport χ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Direct integration against the full positive measure; singular mass
is preserved when the spatial kernel is averaged first. -/
theorem cutoffAverageHeatMass_integral (M : PositiveBilinearMeasure X E)
    {t : ℝ} (ht : 0 < t) (s : Set X) (hs : MeasurableSet s)
    (hbounded : Bornology.IsBounded s) (v : E) :
    ⟪v, cutoffAverageHeatMass μ hQ hk hχ hsχ M ht s hs hbounded v⟫_ℝ =
      ∫ z, χ z * kernelAverage μ ker t s z ∂(M.measure v) := by
  rw [cutoffAverageHeatMass, M.weightedOperator_energy]
  rfl

/-- The averaged source obeys the same Gaussian shell convolution as the
pointwise source, on the original full Bochner measure. -/
theorem scaled_cutoffAverageHeatMass_le_geometric (M : PositiveBilinearMeasure X E)
    (m : ℕ) (p : X) {r t C c T : ℝ} (hr : 0 < r) (ht : 0 < t)
    (s : Set X) (hs : MeasurableSet s) (hbounded : Bornology.IsBounded s)
    (hC : 0 ≤ C) (hc : 0 < c) (hT : 0 ≤ T) (N : ℕ)
    (hlocal : ∀ j ≤ N, ∀ z ∈ dyadicShell p r j,
      χ z * kernelAverage μ ker t s z ≤ (C / r ^ (m + 2)) * gaussianShellFactor c j)
    (htail : ∀ z ∉ ball p (2 ^ N * r), χ z * kernelAverage μ ker t s z ≤ T) (v : E) :
    r ^ 2 * ⟪v, cutoffAverageHeatMass μ hQ hk hχ hsχ M ht s hs hbounded v⟫_ℝ ≤
      C * gaussianMassConvolutionConstant m c *
        (∑ j ∈ Finset.range (N + 1), (3 / 4 : ℝ) ^ j *
          (((2 ^ j * r) ^ 2 / (2 ^ j * r) ^ (m + 2)) *
            (M.measure v).real (ball p (2 ^ j * r)))) +
      r ^ 2 * T * (M.measure v).real univ := by
  rw [cutoffAverageHeatMass_integral]
  apply scaled_integral_le_geometric_mass (M.measure v) m p hr
    ((hχ.mul (kernelAverage_continuous μ hQ hk ht hs hbounded)).integrable_of_hasCompactSupport
      hsχ.mul_right) hC hc hT N hlocal htail

end RegularPointCoordinates

end

end OAI
