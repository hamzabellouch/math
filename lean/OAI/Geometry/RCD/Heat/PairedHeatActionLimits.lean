import OAI.Geometry.RCD.Heat.ScaledHeatActionLimit

namespace OAI

/-! # A common subsequence for the forward and backward heat factors

Both factors retain their actual endpoint laws and noise parameters.
Every interior time has local uniform convergence on this one sequence.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem paired_heat_action_limits (hK : K ≤ 0)
    {S T : Set X} [CompactSpace S] [CompactSpace T]
    (μ : Measure S) (ν : Measure T) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ρ σ : X → ℝ) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hσ0 : ∀ x, 0 ≤ σ x) {B D : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B) (hD : ∀ᵐ x ∂hausdorff n X, |σ x| ≤ D)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (σ x)))
    (F : ℕ → C(S, ℝ)) (G : ℕ → C(T, ℝ))
    (hF : ∀ k a, 0 < F k a) (hG : ∀ k b, 0 < G k b)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0)) (z : X) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a : S, dist z a ≤ R) (hdT : ∀ b : T, dist z b ≤ R) :
    ∃ (U V : HeatActionLimit z) (ι : ℕ → ℕ), StrictMono ι ∧
      hX.CompactHeatConverges hn p μ F ε hε z ι U.potential ∧
      hX.CompactHeatConverges hn p ν G ε hε z ι V.potential := by
  obtain ⟨U,a,ha,hUa⟩ := hX.scaled_heat_action_limit hn p hK
    μ ρ hρ hρ0 hB hμ F hF ε hε hε1 hε0 z hR hdS
  obtain ⟨V,b,hb,hVb⟩ := hX.scaled_heat_action_limit hn p hK
    ν σ hσ hσ0 hD hν (fun k => G (a k)) (fun k => hG (a k))
    (fun k => ε (a k)) (fun k => hε (a k)) (fun k => hε1 (a k))
    (hε0.comp ha.tendsto_atTop) z hR hdT
  refine ⟨U,V,a ∘ b,ha.comp hb,CompactHeatConverges.subsequence hX hn p hUa hb,?_⟩
  exact hVb

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
