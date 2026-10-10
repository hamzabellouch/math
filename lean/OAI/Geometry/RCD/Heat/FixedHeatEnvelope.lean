import OAI.Geometry.RCD.Heat.CompactHeatEnvelope

namespace OAI

/-! # One fixed gauge for every interior heat-envelope slice -/

open Set Filter MeasureTheory Metric TopologicalSpace
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

def forwardGauge (a₀ : S) (hK : K ≤ 0) (hε0 : Tendsto ε atTop (𝓝 0))
    {R : ℝ} (hR : 0 ≤ R) (hdS : ∀ a : S, dist p a ≤ R) : ℝ :=
  let b := Classical.choose (D.forward_envelope a₀ hK hε0 hR hdS)
  D.leftPotential a₀ b-dist p (b:X)^2/4

theorem forward_gauge_envelope (a₀ : S) (hK : K ≤ 0)
    (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a : S, dist p a ≤ R) :
    ∀ t ∈ Ioo (0:ℝ) 1, ∀ x : X, ∃ a ∈ μ.support,
      (∀ d ∈ μ.support, D.leftPotential a₀ d-dist x (d:X)^2/(2*t) ≤
        D.leftPotential a₀ a-dist x (a:X)^2/(2*t)) ∧
      D.forward.potential t x = D.leftPotential a₀ a-dist x (a:X)^2/(2*t)-
        D.forwardGauge a₀ hK hε0 hR hdS :=
  (Classical.choose_spec (D.forward_envelope a₀ hK hε0 hR hdS)).2.2

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
