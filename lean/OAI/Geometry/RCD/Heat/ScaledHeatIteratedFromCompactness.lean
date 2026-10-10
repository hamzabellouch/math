import OAI.Geometry.RCD.Heat.ScaledHeatGlobalCompactness
import OAI.Geometry.RCD.Sobolev.UniformSlicesWeightedIterated

namespace OAI

/-! # Iterated value tests for a prescribed global heat limit

This preserves the exact limit and subsequence supplied by global
compactness, so its value and Sobolev energy limits can be combined.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_iterated_limit_of_compactness (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S, ℝ)) (hF : ∀ k a, 0 < F k a)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (z : X) {R : ℝ} (hR : 0 ≤ R) (hdist : ∀ a : S, dist z a ≤ R)

    (G : ℝ → X → ℝ) (a : ℕ → ℕ) (N : Set ℝ) (hN : N.Countable)
    (hG : Measurable (Function.uncurry G))
    (hdata : ∀ r : ℝ, 0 ≤ r → ∀ δ : ℝ, (hδ : 0 < δ) →
      ∃ (L : ℝ≥0) (M : ℝ), 0 ≤ M ∧ ∀ t, t ∈ Ioo δ 1 → t ∉ N →
        LipschitzOnWith L (G t) (closedBall z r) ∧
        (∀ x ∈ closedBall z r, |G t x| ≤ M) ∧
        TendstoUniformly (fun k (x : closedBall z r) =>
          hX.fixedGaugeScaledPotential hn p ν (F (a k)) (ε (a k)) (hε (a k)) δ hδ z t x)
          (fun x => G t x) atTop) :
    ∀ r : ℝ, 0 ≤ r → ∀ δ : ℝ, (hδ : 0 < δ) →
        ∀ (μ : Measure (closedBall z r)) [IsFiniteMeasure μ],
          ∀ θ : ℝ → ℝ, Integrable θ (volume.restrict (Ioo δ 1)) →
          ∀ φ : closedBall z r → ℝ, Integrable φ μ →
            Tendsto (fun k => ∫ t in Ioo δ 1, θ t * ∫ x,
              φ x*hX.fixedGaugeScaledPotential hn p ν (F (a k)) (ε (a k)) (hε (a k))
                δ hδ z t x ∂μ) atTop
              (𝓝 (∫ t in Ioo δ 1, θ t * ∫ x, φ x*G t x ∂μ)) := by
  intro r hr δ hδ μ _ θ hθ φ hφ
  let Y := closedBall z r
  obtain ⟨_L,M,hM,hgood⟩ := hdata r hr δ hδ
  obtain ⟨D,hD,hbound⟩ := hX.scaled_compact_heat_spacetime_bounded hn p hK
    ν ρ hρ hρ0 hB hν z R hR hdist hδ hr
  let A := M+D
  let f := fun k t (x : Y) =>
    hX.fixedGaugeScaledPotential hn p ν (F (a k)) (ε (a k)) (hε (a k)) δ hδ z t x
  have hi : Measurable (fun q : ℝ × Y => (q.1,(q.2 : X))) :=
    measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
  have hg : Measurable (Function.uncurry (fun t (x : Y) => G t x)) := by
    have hh := hG.comp hi
    dsimp only [Function.comp_def,Function.uncurry] at hh ⊢
    exact hh
  have hf (k : ℕ) : Measurable (Function.uncurry (f k)) := by
    have hm := hX.fixedGaugeScaledPotential_measurable hn p ν ρ hρ hρ0 hB hν
      (F (a k)) (hF (a k)) (hε (a k)) hδ z
    have hh := hm.comp hi
    dsimp only [Function.comp_def,Function.uncurry] at hh
    dsimp only [f,Function.uncurry]
    exact hh
  have hb (k : ℕ) (t : ℝ) (ht : t ∈ Ioo δ 1) (x : Y) : |f k t x| ≤ A := by
    dsimp only [f]
    rw [hX.fixedGaugeScaledPotential_eq hn p ν (F (a k)) (ε (a k)) (hε (a k)) δ hδ z ht.1.le x]
    exact (hbound (F (a k)) (hF (a k)) (hε (a k)) (hε1 (a k)) ht.1.le ht.2.le x x.property).trans
      (le_add_of_nonneg_left hM)
  have hgb (t : ℝ) (ht : t ∈ Ioo δ 1) (htN : t ∉ N) (x : Y) : |G t x| ≤ A :=
    ((hgood t ht htN).2.1 x x.property).trans (le_add_of_nonneg_right hD)
  exact uniform_slices_weighted_iterated_limit μ f (fun t (x : Y) => G t x)
    hf hg hb N hN hgb (fun t ht htN => (hgood t ht htN).2.2) θ hθ φ hφ


end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
