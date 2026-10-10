import OAI.Geometry.RCD.Heat.ScaledHeatAveragedPlan
import OAI.Geometry.RCD.Harmonic.ContinuousHamiltonJacobiComparison

namespace OAI

/-! # Endpoint transport comparison for the original small-noise heat limit -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology ContDiff
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_heat_plan_comparison_of_compactness (hK : K ≤ 0)
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
    let μ := hausdorff n X
    ∀ r : ℝ, 0 < r →
      ∀ (π : Measure C(Time,X)) [IsFiniteMeasure π],
      (∀ᵐ γ ∂π, IsGeodesic γ) →
      ∀ (C : ℝ≥0∞), C ≠ (∞ : ℝ≥0∞) →
      (∀ t : Time, π.map (fun γ => γ t) ≤ C • μ) →
      MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π →
      (∀ t : Time, ∀ᵐ γ ∂π, γ t ∈ closedBall z r) →
      ∀ a b : ℝ, 0 < a → a < b → b < 1 →
        (∫ γ : C(Time,X), H a (γ 0) ∂π) - (∫ γ : C(Time,X), H b (γ 1) ∂π) ≤
          (∫ γ : C(Time,X), (dist (γ 0) (γ 1))^2 ∂π)/(2*(b-a)) := by
  intro H μ r hr π _ hgeo C hC hcomp hLength hs a b ha hab hb
  let δ := a/2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδa : δ < a := by dsimp only [δ]; linarith
  have hδ1 : δ ≤ 1 := by dsimp only [δ]; linarith
  obtain ⟨_,hm,hlocal,_⟩ := hX.scaled_heat_averaged_gradient_of_compactness hn p hK
    ν ρ hρ hρ0 hB hν F hF ε hε hε1 hε0 z hR hdist G ι hι N hN hG hdata
  obtain ⟨L,hL⟩ := hlocal r hr δ hδ
  apply continuous_comparison_of_time_averages π H hm (isCompact_closedBall z r) hL
    (fun γ => γ 0) (fun γ => γ 1) (measurable_path_eval 0) (measurable_path_eval 1)
    (hs 0) (hs 1) hδa hab hb
  intro h hh hha hhb
  exact hX.scaled_heat_averaged_plan_comparison_of_compactness hn p hK
    ν ρ hρ hρ0 hB hν F hF ε hε hε1 hε0 z hR hdist G ι hι N hN hG hdata
    (4*r) (by positivity) δ hδ hδ1 π hgeo C hC hcomp hLength
    (fun t => by simpa only [show 4*r/4=r by ring] using hs t) h a b hh hab hha hhb

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
