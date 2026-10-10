import OAI.Analysis.LipschitzHilbert.Phase.LineGridPrediction
import OAI.Analysis.LipschitzHilbert.Trees.SourceAveraging

namespace OAI

/-! Construct the snapshot predictor at the manuscript's averaging scale.
The near-uniform probability and its remainder are supplied by the
Fourier kernel construction, before the graph and line grid are chosen. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem exists_source_grid_prediction :
    ∃ C L0 : ℝ, 1 ≤ C ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (grid : FiniteLineGrid) (level : ℕ), level ≤ grid.depth →
      ∀ (G : ι → ι → Prop), (∀ ⦃i j⦄, G i j → G j i) →
      ∀ (w m : ι → ℝ), (∀ i, 0 < w i) →
      (∀ i, orderMass w (closedNeighborhood G i) ≤ m i) →
      ∀ (frequency : ι → κ → ℝ) (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
        (lambda : ι → ℂ) (i₀ : ι) (D p K u freqBound θ : ℝ),
      1 ≤ D → 4 ≤ p →
      (∀ i j, i ≠ j → ¬G i j → ∀ k,
        1/(grid.width*SourceParameters.step L^(-(1/8:ℝ))) ≤
          |frequency i k-frequency j k|) →
      (∀ S : Finset ι, (S : Set ι).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) →
      (∀ i, 0 ≤ l i) → (∑ i, l i) ≤ 1 →
      (∀ i, ‖lambda i‖ ≤ (w i/m i)^phaseMu D p) →
      0 ≤ K → 0 ≤ u → 0 ≤ freqBound →
      (∑ i : RemainderIndex i₀, ‖predictionCoefficients l X lambda D p i‖) ≤ K*u →
      (∀ i : RemainderIndex i₀, ∀ j, |frequency i j-frequency i₀ j| ≤ freqBound) →
      0 ≤ θ → θ ≤ 1 →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ t, 0 ≤ Γ t) ∧
        (∫ t, Γ t ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ s t, grid.index level s = grid.index level t → Γ s = Γ t) ∧
        ∀ t ∈ grid.root, (1-θ)*graphPredictionValue frequency l X lambda D p t+θ ≤
          Real.exp ((4*C*SourceParameters.step L^(-(1/16:ℝ))*p*K+
            p*freqBound*K*(grid.width/(grid.branching:ℝ)^level))*u)*Γ t := by
  obtain ⟨C,hC,haverage⟩ := exists_source_averaging_constant
  obtain ⟨L0,hL0⟩ := eventually_atTop.mp haverage
  refine ⟨C,L0,hC,?_⟩
  intro L hL ι κ _ _ grid level hlevel G hG w m hw hm frequency l X lambda i₀
    D p K u freqBound θ hD hp hfrequency hcard hl htotal hlambda hK hu hfreq hmass hfreqBound hθ0 hθ1
  obtain ⟨eta,remainder,heta,hetaC,hetahalf,hremainder,hnu⟩ :=
    hL0 L hL grid.origin (grid.origin+grid.width) (by linarith [grid.width_pos])
  have hwidth : grid.origin+grid.width-grid.origin = grid.width := by ring
  rw [hwidth] at hnu
  let := hremainder
  have hgap : 0 < 1/(grid.width*SourceParameters.step L^(-(1/8:ℝ))) := by
    have := grid.width_pos
    have := SourceParameters.step_pos L
    positivity
  obtain ⟨Γ,hmeas,hint,hpos,havg,hcell,hpoint⟩ := grid.graph_prediction_step level hlevel
    G hG w m hw hm remainder frequency l X lambda i₀ heta.le (by linarith) hgap hnu hD hp
    hfrequency hcard hl htotal hlambda hK hu hfreq hmass hfreqBound hθ0 hθ1
  refine ⟨Γ,hmeas,hint,hpos,havg,hcell,?_⟩
  have hp0 : 0 ≤ p := by linarith
  have hfactor : eta/(1-eta) ≤ 2*eta := by
    apply (div_le_iff₀ (by linarith : 0 < 1-eta)).mpr
    nlinarith
  have herror : eta/(1-eta)*(2*p*K) ≤ 4*C*SourceParameters.step L^(-(1/16:ℝ))*p*K := by
    calc
      _ ≤ (2*eta)*(2*p*K) := mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ ≤ (2*(C*SourceParameters.step L^(-(1/16:ℝ))))*(2*p*K) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hetaC (by norm_num)) (by positivity)
      _ = _ := by ring
  intro t ht
  apply (hpoint t ht).trans
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (add_le_add_left herror _) hu)) (hpos t)

end LipschitzHilbert

end

end OAI
