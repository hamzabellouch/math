import OAI.Geometry.RCD.Heat.HeatGeneratorAmplitude
import OAI.Geometry.RCD.Harmonic.ProbabilityDensityPairing

namespace OAI

/-! # The test-Laplacian remainder is bounded independently of the bridge -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p in
theorem heat_second_source_pairing_bound (hK : K ≤ 0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a : ℝ} (ha : 0 < a)
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    [IsProbabilityMeasure ((hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))] :
    |∫ x, heatSecondGeneratorAt (hausdorff n X) hX.quadratic a f x*ρ x ∂hausdorff n X| ≤
      (2*(n:ℝ)*(|K|+1/(a/2)))^2*(A:ℝ) :=
  probability_density_pairing_bound (hausdorff n X) hρ hρ0
    (hX.heatSecondGeneratorAt_amplitude hn p hK f A hf ha)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
