import OAI.Geometry.RCD.Heat.CompactHeatScalingDensity

namespace OAI

/-! # Scalar means of the actual compact heat interpolation -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

def interpolationMean (w : X → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∫ x, w x *
    ((∫ y, hX.canonicalHeatKernel hn p (ε k/4*t) x y * D.left k y ∂μ) *
      (∫ z, hX.canonicalHeatKernel hn p (ε k/4*(1-t)) x z * D.right k z ∂ν))
      ∂hausdorff n X

theorem interpolationMean_eq_density (w : X → ℝ) (k : ℕ) (t : Ioo (0 : ℝ) 1) :
    D.interpolationMean w k t = ∫ x, w x*D.interpolationDensity k t x ∂hausdorff n X := rfl

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
