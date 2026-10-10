import OAI.Geometry.RCD.Heat.CompactHeatEnvelope
import OAI.Geometry.RCD.Heat.CompactHeatScalingCoupling
import OAI.Geometry.RCD.Harmonic.DualSegmentEnvelope

namespace OAI

/-! # Affine heat-action values on saturated transport segments -/

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

theorem forward_segment_values (a₀ : S) (b₀ : T) (c : ℝ) (hK : K ≤ 0)
    (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a : S, dist p a ≤ R)
    (hdual : ∀ a b, b ∈ ν.support → D.slack a₀ b₀ c (a,b) ≤ 0) :
    ∃ A : ℝ, ∀ a ∈ μ.support, ∀ b ∈ ν.support,
      D.slack a₀ b₀ c (a,b)=0 → ∀ s ∈ Ioo (0:ℝ) 1, ∀ x : X,
      dist x (a : X)=s*dist (a : X) (b : X) →
      dist x (b : X)=(1-s)*dist (a : X) (b : X) →
      D.forward.potential (s/2) x=D.leftPotential a₀ a-s*dist (a : X) (b : X)^2-A := by
  obtain ⟨r,_,_,hE⟩ := D.forward_envelope a₀ hK hε0 hR hdS
  let A := D.leftPotential a₀ r-dist p (r : X)^2/4
  refine ⟨A,?_⟩
  intro a ha b hb hz s hs x hxa hxb
  have hhalf : s/2 ∈ Ioo (0:ℝ) 1 := ⟨half_pos hs.1,by linarith [hs.2]⟩
  obtain ⟨m,_,hm,hval⟩ := hE (s/2) hhalf x
  have he : 2*(s/2)=s := by ring
  simp only [he] at hm hval
  have hbound (u : S) : D.leftPotential a₀ u+(D.rightPotential b₀ b+c) ≤ dist (u : X) (b : X)^2 := by
    have hh := hdual u b hb
    change D.leftPotential a₀ u-dist (u : X) (b : X)^2+D.rightPotential b₀ b+c ≤ 0 at hh
    linarith
  have heq : D.leftPotential a₀ a+(D.rightPotential b₀ b+c)=dist (a : X) (b : X)^2 := by
    change D.leftPotential a₀ a-dist (a : X) (b : X)^2+D.rightPotential b₀ b+c=0 at hz
    linarith
  have hv := dual_segment_envelope (D.leftPotential a₀) a m b x
    (D.rightPotential b₀ b+c) s hs.1 hs.2.le hbound heq hxa hxb (hm a ha)
  rw [hv] at hval
  exact hval

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
