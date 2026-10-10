import OAI.Geometry.RCD.Heat.ScaledHeatContinuousCylinder
import OAI.Geometry.RCD.Sobolev.ContinuousTimeCylinders

namespace OAI

/-! # One continuous representative of the prescribed global heat limit

The same good-time limit extends through its exceptional times. Both the
time and space Lipschitz constants are uniform on each interior cylinder.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_continuous_limit_of_compactness (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S, ℝ)) (hF : ∀ k a, 0 < F k a)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (z : X) {R : ℝ} (hR : 0 ≤ R) (hdist : ∀ a : S, dist z a ≤ R)
    (G : ℝ → X → ℝ) (ι : ℕ → ℕ) (hι : StrictMono ι) (N : Set ℝ) (hN : N.Countable)
    (hdata : ∀ r : ℝ, 0 ≤ r → ∀ δ : ℝ, (hδ : 0 < δ) →
      ∃ (L : ℝ≥0) (M : ℝ), 0 ≤ M ∧ ∀ t, t ∈ Ioo δ 1 → t ∉ N →
        LipschitzOnWith L (G t) (closedBall z r) ∧
        (∀ x ∈ closedBall z r, |G t x| ≤ M) ∧
        TendstoUniformly (fun k (x : closedBall z r) =>
          hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t x)
          (fun x => G t x) atTop)
    :
    let H := goodTimeExtension N G
    ContinuousOn (Function.uncurry H) (Ioo 0 1 ×ˢ univ) ∧
      Measurable (Function.uncurry H) ∧
      (∀ r : ℝ, 0 < r → ∀ δ : ℝ, 0 < δ →
        ∃ L : ℝ≥0, LipschitzOnWith L (Function.uncurry H) (Ioo δ 1 ×ˢ closedBall z r)) ∧
      ∀ t ∈ Ioo 0 1, t ∉ N → ∀ x, H t x = G t x := by
  intro H
  have hlocal (r : ℝ) (hr : 0 < r) (δ : ℝ) (hδ : 0 < δ) :
      ∃ M : ℝ≥0, LipschitzOnWith M (Function.uncurry H) (Ioo δ 1 ×ˢ closedBall z r) := by
    obtain ⟨U,C,L,htime,_hspace,heq,hU⟩ :=
      hX.scaled_heat_continuous_cylinder_of_compactness hn p hK ν ρ hρ hρ0 hB hν
        F hF ε hε hε1 hε0 z hR hdist G ι hι N hN hdata hr hδ
    have he (t : ℝ) (ht : t ∈ Ioo δ 1) (x : closedBall z r) : H t x = U t x :=
      goodTimeExtension_eq_local_subtype (closedBall z r) N hN G U hδ
        (fun x => (htime x).continuous) heq ht x
    refine ⟨C+L,LipschitzOnWith.of_dist_le_mul ?_⟩
    intro q hq q' hq'
    change dist (H q.1 q.2) (H q'.1 q'.2) ≤ _
    rw [he q.1 hq.1 ⟨q.2,hq.2⟩,he q'.1 hq'.1 ⟨q'.2,hq'.2⟩]
    exact hU.dist_le_mul (q.1,⟨q.2,hq.2⟩) ⟨hq.1,mem_univ _⟩
      (q'.1,⟨q'.2,hq'.2⟩) ⟨hq'.1,mem_univ _⟩
  obtain ⟨hc,hm⟩ := goodTimeExtension_regular z N G hlocal
  refine ⟨hc,hm,hlocal,?_⟩
  intro t ht htN x
  let r := dist x z+1
  have hr : 0 < r := by dsimp only [r]; positivity
  have hx : x ∈ closedBall z r := by simp only [mem_closedBall,r]; linarith
  have hδ : 0 < t/2 := half_pos ht.1
  have htt : t ∈ Ioo (t/2) 1 := ⟨by linarith [ht.1],ht.2⟩
  obtain ⟨U,C,_L,htime,_hspace,heq,_hU⟩ :=
    hX.scaled_heat_continuous_cylinder_of_compactness hn p hK ν ρ hρ hρ0 hB hν
      F hF ε hε hε1 hε0 z hR hdist G ι hι N hN hdata hr hδ
  exact (goodTimeExtension_eq_local_subtype (closedBall z r) N hN G U hδ
    (fun x => (htime x).continuous) heq htt ⟨x,hx⟩).trans (heq t htt htN ⟨x,hx⟩)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
