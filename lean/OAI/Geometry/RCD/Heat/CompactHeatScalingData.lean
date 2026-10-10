import OAI.Geometry.RCD.Heat.CompactScalingActionLimits
import OAI.Geometry.RCD.Heat.HeatActionSlices

namespace OAI

/-! # Data of the constructed compact heat scaling sequence -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]

structure CompactHeatScalingData (μ : Measure S) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) where
  left : ℕ → C(S,ℝ)
  right : ℕ → C(T,ℝ)
  forward : HeatActionLimit p
  backward : HeatActionLimit p
  index : ℕ → ℕ
  strict : StrictMono index
  left_pos : ∀ k a, 0 < left k a
  right_pos : ∀ k b, 0 < right k b
  row : ∀ k a, left k a*(∫ b, hX.canonicalHeatKernel hn p (ε k/4) a b*right k b ∂ν)=1
  col : ∀ k b, right k b*(∫ a, hX.canonicalHeatKernel hn p (ε k/4) a b*left k a ∂μ)=1
  forward_limit : hX.CompactHeatConverges hn p μ left ε hε p index forward.potential
  backward_limit : hX.CompactHeatConverges hn p ν right ε hε p index backward.potential
  left_limit : ∀ a₀ : S, TendstoUniformly
    (fun k a => ε (index k)*(Real.log (left (index k) a)-Real.log (left (index k) a₀)))
    (fun a => backward.potential (1/2) a₀-backward.potential (1/2) a) atTop
  right_limit : ∀ b₀ : T, TendstoUniformly
    (fun k b => ε (index k)*(Real.log (right (index k) b)-Real.log (right (index k) b₀)))
    (fun b => forward.potential (1/2) b₀-forward.potential (1/2) b) atTop

theorem exists_compact_heat_scaling_data (hK : K ≤ 0) (a₀ : S) (b₀ : T)
    (μ : Measure S) (ν : Measure T) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ρ σ : X → ℝ) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hσ0 : ∀ x, 0 ≤ σ x) {B D : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B) (hD : ∀ᵐ x ∂hausdorff n X, |σ x| ≤ D)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (σ x)))
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a : S, dist p a ≤ R) (hdT : ∀ b : T, dist p b ≤ R) :
    Nonempty (hX.CompactHeatScalingData hn p μ ν ε hε) := by
  obtain ⟨F,G,U,V,ι,hF,hG,hr,hc,hι,hU,hV,hl,hh,_⟩ :=
    hX.compact_scaling_action_limits hn p hK ⟨a₀,a₀.property⟩ ⟨b₀,b₀.property⟩
      μ ν ρ σ hρ hσ hρ0 hσ0 hB hD hμ hν ε hε hε1 hε0 p hR hdS hdT
  exact ⟨⟨F,G,U,V,ι,hι,hF,hG,hr,hc,hU,hV,hl,hh⟩⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
