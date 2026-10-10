import OAI.Geometry.RCD.Heat.ScaledHeatAllTimes

namespace OAI

/-! # Continuous action limits with convergence at every interior time -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

structure HeatActionLimit (z : X) where
  potential : ℝ → X → ℝ
  continuous : ContinuousOn (Function.uncurry potential) (Ioo 0 1 ×ˢ univ)
  measurable : Measurable (Function.uncurry potential)
  local_lipschitz : ∀ r : ℝ, 0 < r → ∀ δ : ℝ, 0 < δ →
    ∃ L : ℝ≥0, LipschitzOnWith L (Function.uncurry potential) (Ioo δ 1 ×ˢ closedBall z r)
  action : ∀ a b : ℝ, 0 < a → a < b → b < 1 → ∀ x y : X,
    potential a x-potential b y ≤ (dist x y)^2/(2*(b-a))

namespace NoncollapsedRCD
variable [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

def CompactHeatConverges {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (F : ℕ → C(S, ℝ))
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (z : X) (ι : ℕ → ℕ) (H : ℝ → X → ℝ) : Prop :=
  ∀ r : ℝ, 0 ≤ r → ∀ δ : ℝ, (hδ : 0 < δ) → ∀ t ∈ Ioo δ 1,
    TendstoUniformly (fun k (x : closedBall z r) =>
      hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t x)
      (fun x => H t x) atTop

theorem CompactHeatConverges.subsequence {S : Set X} [CompactSpace S]
    {ν : Measure S} [IsProbabilityMeasure ν] {F : ℕ → C(S, ℝ)}
    {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k} {z : X} {ι σ : ℕ → ℕ} {H : ℝ → X → ℝ}
    (h : hX.CompactHeatConverges hn p ν F ε hε z ι H) (hσ : StrictMono σ) :
    hX.CompactHeatConverges hn p ν F ε hε z (ι ∘ σ) H := by
  intro r hr δ hδ t ht
  apply Metric.tendstoUniformly_iff.mpr
  intro η hη
  exact hσ.tendsto_atTop.eventually ((Metric.tendstoUniformly_iff.mp (h r hr δ hδ t ht)) η hη)

theorem scaled_heat_action_limit (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S, ℝ)) (hF : ∀ k a, 0 < F k a)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (z : X) {R : ℝ} (hR : 0 ≤ R) (hdist : ∀ a : S, dist z a ≤ R) :
    ∃ (H : HeatActionLimit z) (ι : ℕ → ℕ), StrictMono ι ∧
      hX.CompactHeatConverges hn p ν F ε hε z ι H.potential := by
  obtain ⟨H,ι,N,hι,hN,hc,hm,hl,hs,ha,_hp⟩ := hX.scaled_heat_transport_limit hn p hK
    ν ρ hρ hρ0 hB hν F hF ε hε hε1 hε0 z hR hdist
  refine ⟨⟨H,hc,hm,hl,ha⟩,ι,hι,?_⟩
  intro r hr δ hδ t ht
  exact hX.scaled_heat_uniform_all_times hn p hK ν ρ hρ hρ0 hB hν F hF ε hε hε1 hε0
    z H ι hι N hN hl hs hr hδ ht

end NoncollapsedRCD
end RegularPointCoordinates

end

end OAI
