import OAI.Geometry.RCD.Heat.CompactHeatScalingCoupling
import OAI.Geometry.RCD.Heat.ContinuousKernelSaturation
import OAI.Geometry.RCD.Transport.CompactDualCost

namespace OAI

/-! # Saturated optimal limits of the actual heat-kernel couplings

The kernel scaling, exact marginals, common action subsequence and dual
potentials are all constructed. No optimality or dual-saturation input is
used. The cost retains the original ambient metric.
-/

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

theorem saturated_limit (a₀ : S) (b₀ : T) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a : S, dist p a ≤ R) (hdT : ∀ b : T, dist p b ≤ R) :
    ∃ (c : ℝ) (Q : ProbabilityMeasure (S × T)) (j : ℕ → ℕ), StrictMono j ∧
      Tendsto (fun k => D.coupling (j k)) atTop (𝓝 Q) ∧
      (Q : Measure (S × T)).map Prod.fst=μ ∧ (Q : Measure (S × T)).map Prod.snd=ν ∧
      (∀ᵐ z ∂(Q : Measure (S × T)), D.slack a₀ b₀ c z=0) ∧
      ∀ π : Measure (S × T), π.map Prod.fst=μ → π.map Prod.snd=ν →
        (∫ z, dist (z.1 : X) (z.2 : X)^2 ∂(Q : Measure (S × T))) ≤
          ∫ z, dist (z.1 : X) (z.2 : X)^2 ∂π := by
  obtain ⟨c,hc,hd,_⟩ := D.dual_limit a₀ b₀ hK hε1 hε0 hR hdS hdT
  obtain ⟨Q,j,hj,hQ,hl,hr,hs⟩ := continuous_kernel_saturation μ ν D.density D.density_pos
    D.density_row D.density_col (fun k => ε (D.index k)) (fun k => (hε (D.index k)).le)
    (D.slack a₀ b₀ c) hd (D.density_log_limit a₀ b₀ c hK hε1 hε0 hR hdS hdT hc)
  refine ⟨c,Q,j,hj,hQ,hl,hr,hs,?_⟩
  let cost : C(S × T,ℝ) := ⟨fun z => dist (z.1 : X) (z.2 : X)^2,by fun_prop⟩
  apply compact_dual_cost_minimizer μ ν Q hl hr (D.leftPotential a₀) (D.rightPotential b₀) cost c
  · intro a b hb
    have hh := hd a b hb
    change D.leftPotential a₀ a+D.rightPotential b₀ b+c ≤ dist (a : X) (b : X)^2
    linarith
  · filter_upwards [hs] with z hz
    change D.leftPotential a₀ z.1-dist (z.1 : X) (z.2 : X)^2+D.rightPotential b₀ z.2+c=0 at hz
    change D.leftPotential a₀ z.1+D.rightPotential b₀ z.2+c=dist (z.1 : X) (z.2 : X)^2
    linarith

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
