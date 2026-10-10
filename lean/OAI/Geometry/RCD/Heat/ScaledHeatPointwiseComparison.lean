import OAI.Geometry.RCD.Heat.ScaledHeatPlanComparison
import OAI.Geometry.RCD.Transport.PointwisePlanComparison

namespace OAI

/-! # Pointwise action comparison for the original small-noise heat limit -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology ContDiff
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_pointwise_comparison_of_compactness (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S,ℝ)) (hF : ∀ k a, 0 < F k a)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (z : X) {R : ℝ} (hR : 0 ≤ R) (hdist : ∀ a : S, dist z a ≤ R)
    (G : ℝ → X → ℝ) (ι : ℕ → ℕ) (hι : StrictMono ι) (N : Set ℝ) (hN : N.Countable)
    (hG : Measurable (Function.uncurry G))
    (hdata : ∀ r : ℝ, 0 ≤ r → ∀ δ : ℝ, (hδ : 0 < δ) →
      ∃ (L : ℝ≥0) (M : ℝ), 0 ≤ M ∧ ∀ t, t ∈ Ioo δ 1 → t ∉ N →
        LipschitzOnWith L (G t) (closedBall z r) ∧
        (∀ x ∈ closedBall z r, |G t x| ≤ M) ∧
        TendstoUniformly (fun k (x : closedBall z r) =>
          hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t x)
          (fun x => G t x) atTop) :
    let H := goodTimeExtension N G
    ∀ a b : ℝ, 0 < a → a < b → b < 1 → ∀ x y : X,
      H a x-H b y ≤ (dist x y)^2/(2*(b-a)) := by
  intro H a b ha hab hb x y
  obtain ⟨_,hm,hlocal,_⟩ := hX.scaled_heat_continuous_limit_of_compactness hn p hK
    ν ρ hρ hρ0 hB hν F hF ε hε hε1 hε0 z hR hdist G ι hι N hN hdata
  have hmeas (t : ℝ) : Measurable (H t) :=
    hm.comp (measurable_const.prodMk measurable_id)
  have hLip : ∀ r : ℝ, 0 < r → ∃ L : ℝ≥0,
      LipschitzOnWith L (H a) (closedBall z r) ∧ LipschitzOnWith L (H b) (closedBall z r) := by
    intro r hr
    obtain ⟨L,hL⟩ := hlocal r hr (a/2) (by positivity)
    have hs (t : ℝ) (ht : t ∈ Ioo (a/2) 1) : LipschitzOnWith L (H t) (closedBall z r) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro u hu v hv
      have hh := hL.dist_le_mul (t,u) ⟨ht,hu⟩ (t,v) ⟨ht,hv⟩
      simpa only [Function.uncurry,Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using hh
    exact ⟨L,hs a ⟨by linarith,hab.trans hb⟩,hs b ⟨by linarith,hb⟩⟩
  apply hX.pointwise_comparison_of_plans hn z (H a) (H b) (hmeas a) (hmeas b)
    (sub_pos.mpr hab) hLip ?_ x y
  intro r hr π _ hgeo C hC hcomp hLength hs
  exact hX.scaled_heat_plan_comparison_of_compactness hn p hK
    ν ρ hρ hρ0 hB hν F hF ε hε hε1 hε0 z hR hdist G ι hι N hN hG hdata
    r hr π hgeo C hC hcomp hLength hs a b ha hab hb

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
