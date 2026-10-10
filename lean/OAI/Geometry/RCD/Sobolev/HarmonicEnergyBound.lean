import OAI.Geometry.RCD.Sobolev.LocalBochnerInput

namespace OAI

/-! # Enlarging the bound of a fixed harmonic energy representative -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The energy function and its full measure equation are unchanged. -/
def LocalHarmonicEnergy.enlargeBound {U : E →L[ℝ] SobolevSpace μ hQ}
    {M : PositiveBilinearMeasure X E} {κ : ℝ} {p : X} {r : ℝ} {L H : ℝ≥0} {v : E}
    (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (hLH : (L : ℝ) ^ 2 ≤ (H : ℝ) ^ 2) : LocalHarmonicEnergy μ hQ U M κ p r H v where
  energy := G.energy
  representative := G.representative
  bounded := by
    filter_upwards [G.bounded] with x hx
    exact hx.trans (by
      simp only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm]
      exact mul_le_mul_of_nonneg_right hLH (sq_nonneg ‖v‖))
  measure_laplacian := G.measure_laplacian

end RegularPointCoordinates

end

end OAI
