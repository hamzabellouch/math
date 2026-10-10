import OAI.Geometry.RCD.Heat.ScaledHeatGlobalCompactness
import OAI.Geometry.RCD.Heat.ScaledHeatPointwiseComparison

namespace OAI

/-! # A continuous transport limit of the actual scaled heat potentials

One subsequence and one exceptional countable time set serve every
compact spatial ball. The original continuous limit satisfies the
endpoint comparison for every bounded compressed geodesic plan.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_transport_limit (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S, ℝ)) (hF : ∀ k a, 0 < F k a)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (z : X) {R : ℝ} (hR : 0 ≤ R) (hdist : ∀ a : S, dist z a ≤ R) :
    ∃ (H : ℝ → X → ℝ) (ι : ℕ → ℕ) (N : Set ℝ),
      StrictMono ι ∧ N.Countable ∧
      ContinuousOn (Function.uncurry H) (Ioo 0 1 ×ˢ univ) ∧
      Measurable (Function.uncurry H) ∧
      (∀ r : ℝ, 0 < r → ∀ δ : ℝ, 0 < δ →
        ∃ L : ℝ≥0, LipschitzOnWith L (Function.uncurry H) (Ioo δ 1 ×ˢ closedBall z r)) ∧
      (∀ r : ℝ, 0 ≤ r → ∀ δ : ℝ, (hδ : 0 < δ) →
        ∀ t ∈ Ioo δ 1, t ∉ N →
          TendstoUniformly (fun k (x : closedBall z r) =>
            hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t x)
            (fun x => H t x) atTop) ∧
      (∀ a b : ℝ, 0 < a → a < b → b < 1 → ∀ x y : X,
        H a x-H b y ≤ (dist x y)^2/(2*(b-a))) ∧
      ∀ r : ℝ, 0 < r →
      ∀ (π : Measure C(Time,X)) [IsFiniteMeasure π],
      (∀ᵐ γ ∂π, IsGeodesic γ) →
      ∀ (C : ℝ≥0∞), C ≠ (∞ : ℝ≥0∞) →
      (∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X) →
      MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π →
      (∀ t : Time, ∀ᵐ γ ∂π, γ t ∈ closedBall z r) →
      ∀ a b : ℝ, 0 < a → a < b → b < 1 →
        (∫ γ : C(Time,X), H a (γ 0) ∂π) - (∫ γ : C(Time,X), H b (γ 1) ∂π) ≤
          (∫ γ : C(Time,X), (dist (γ 0) (γ 1))^2 ∂π)/(2*(b-a)) := by
  obtain ⟨G,ι,N,hι,hN,hG,hdata⟩ := hX.scaled_heat_global_compactness hn p hK
    ν ρ hρ hρ0 hB hν F hF ε hε hε1 hε0 z hR hdist
  let H := goodTimeExtension N G
  obtain ⟨hc,hm,hlocal,hagree⟩ := hX.scaled_heat_continuous_limit_of_compactness hn p hK
    ν ρ hρ hρ0 hB hν F hF ε hε hε1 hε0 z hR hdist G ι hι N hN hdata
  refine ⟨H,ι,N,hι,hN,hc,hm,hlocal,?_,?_,?_⟩
  · intro r hr δ hδ t ht htN
    obtain ⟨_,_,_,hs⟩ := hdata r hr δ hδ
    have he : (fun x : closedBall z r => G t x) = (fun x : closedBall z r => H t x) :=
      funext fun x => (hagree t ⟨hδ.trans ht.1,ht.2⟩ htN x).symm
    rw [← he]
    exact (hs t ht htN).2.2
  · exact hX.scaled_heat_pointwise_comparison_of_compactness hn p hK
      ν ρ hρ hρ0 hB hν F hF ε hε hε1 hε0 z hR hdist G ι hι N hN hG hdata
  · exact hX.scaled_heat_plan_comparison_of_compactness hn p hK
      ν ρ hρ hρ0 hB hν F hF ε hε hε1 hε0 z hR hdist G ι hι N hN hG hdata

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
