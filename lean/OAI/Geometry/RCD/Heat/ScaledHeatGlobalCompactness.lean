import OAI.Geometry.RCD.Heat.ScaledHeatCountableRegions
import OAI.Geometry.RCD.Heat.HeatCylinderGluing
import OAI.Geometry.RCD.Heat.HeatExhaustionScales

namespace OAI

/-! # One global measurable limit of the actual scaled heat potentials

On every compact spatial ball and every positive interior time interval,
the same subsequence converges uniformly in space outside one countable
exceptional set of times. The limiting function is locally Lipschitz in
space at those times.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_global_compactness (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S, ℝ)) (hF : ∀ k a, 0 < F k a)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (z : X) {R : ℝ} (hR : 0 ≤ R) (hdist : ∀ a : S, dist z a ≤ R) :
    ∃ (G : ℝ → X → ℝ) (a : ℕ → ℕ) (N : Set ℝ), StrictMono a ∧ N.Countable ∧
      Measurable (Function.uncurry G) ∧
      ∀ r : ℝ, 0 ≤ r → ∀ δ : ℝ, (hδ : 0 < δ) →
        ∃ (L : ℝ≥0) (M : ℝ), 0 ≤ M ∧ ∀ t, t ∈ Ioo δ 1 → t ∉ N →
          LipschitzOnWith L (G t) (closedBall z r) ∧
          (∀ x ∈ closedBall z r, |G t x| ≤ M) ∧
          TendstoUniformly (fun k (x : closedBall z r) =>
            hX.fixedGaugeScaledPotential hn p ν (F (a k)) (ε (a k)) (hε (a k)) δ hδ z t x)
            (fun x => G t x) atTop := by
  obtain ⟨L,M,g,a,N,ha,hN,hg,hcompat⟩ := hX.scaled_heat_countable_regions hn p hK
    ν ρ hρ hρ0 hB hν F hF ε hε hε1 hε0 z hR hdist
    heatCompactRadius heatCompactTimeMargin heatCompactRadius_nonneg
    heatCompactTimeMargin_pos heatCompactTimeMargin_le_one
  obtain ⟨G,hG,hGeq⟩ := glue_heat_cylinder_limits z heatCompactRadius heatCompactTimeMargin N hN g
    (fun m t => ((hg m).2.1 t).continuous) (fun m => (hg m).2.2.1) hcompat
  refine ⟨G,a,N,ha,hN,hG,?_⟩
  intro r hr δ hδ
  obtain ⟨m,hrm,hδm⟩ := heat_exhaustion_contains r hδ
  have hinc : closedBall z r ⊆ closedBall z (heatCompactRadius m) := closedBall_subset_closedBall hrm
  have hM : 0 ≤ M m := (abs_nonneg (g m 0
    ⟨z,mem_closedBall_self (heatCompactRadius_nonneg m)⟩)).trans
      ((hg m).1 0 ⟨z,mem_closedBall_self (heatCompactRadius_nonneg m)⟩)
  refine ⟨L m,M m,hM,?_⟩
  intro t ht htN
  have hmt : t ∈ Ioo (heatCompactTimeMargin m) 1 := ⟨hδm.trans ht.1,ht.2⟩
  have heq (x : X) (hx : x ∈ closedBall z r) :
      G t x = g m t ⟨x,hinc hx⟩ := hGeq m t hmt htN x (hinc hx)
  refine ⟨?_,?_,?_⟩
  · intro x hx y hy
    rw [heq x hx,heq y hy]
    exact (hg m).2.1 t ⟨x,hinc hx⟩ ⟨y,hinc hy⟩
  · intro x hx
    rw [heq x hx]
    exact (hg m).1 t ⟨x,hinc hx⟩
  · let i : closedBall z r → closedBall z (heatCompactRadius m) := fun x => ⟨x,hinc x.property⟩
    have hh := ((hg m).2.2.2 t hmt htN).comp i
    have hu : (fun k (x : closedBall z r) =>
        hX.fixedGaugeScaledPotential hn p ν (F (a k)) (ε (a k)) (hε (a k)) δ hδ z t x) =
        (fun k (x : closedBall z r) => hX.fixedGaugeScaledPotential hn p ν
          (F (a k)) (ε (a k)) (hε (a k)) (heatCompactTimeMargin m)
          (heatCompactTimeMargin_pos m) z t (i x)) := by
      funext k x
      simp only [fixedGaugeScaledPotential,max_eq_right ht.1.le,max_eq_right hmt.1.le,i]
    have hv : (fun x : closedBall z r => G t x) = (fun x => g m t (i x)) :=
      funext fun x => heq x x.property
    rw [hu,hv]
    exact hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
