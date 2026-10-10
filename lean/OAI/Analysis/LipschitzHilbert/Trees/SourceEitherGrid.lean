import OAI.Analysis.LipschitzHilbert.Trees.SourceGridParameters

namespace OAI

/-! The balanced and dominant source constructions give one marked
predictor. Dominant-path hypotheses are only needed when the drop is small. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem eventually_source_grid_parameters (C F : ℝ) (hC : 0 ≤ C) (hF : 0 ≤ F) :
    ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ, 1 ≤ D → 0 < N → Real.log N ≤ 2*L →
    let p := Real.sqrt L
    let K := L^C*(1+N^phaseMu D p)
    let ε := SourceParameters.step L^(-(1/8:ℝ))
    let θ := SourceParameters.step L^(-(1/16:ℝ))
    ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (grid : FiniteLineGrid) (level : ℕ), level ≤ grid.depth →
    ∀ (G : ι → ι → Prop), (∀ ⦃i j⦄, G i j → G j i) →
    ∀ (c m : ι → ℝ) (n : ℝ), (∀ i, 0 < c i) → 0 < n →
      (∀ i, orderMass c (closedNeighborhood G i) ≤ m i) → (∑ i, c i/n) ≤ 1 →
    ∀ (frequency : ι → κ → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
      (i₀ : ι) (Aconst freqBound u q : ℝ),
      0 ≤ Aconst → 0 ≤ freqBound → 0 ≤ u →
      n^phaseMu D p ≤ K → Aconst*n^phaseMu D p ≤ K →
      (∀ i, ‖A i‖ ≤ Aconst*c i) → (∀ i, ‖lam i‖ ≤ 1) →
      (∀ i, ‖lam i‖ ≤ (c i/m i)^phaseMu D p) →
      (∑ i : RemainderIndex i₀, c i/n) ≤ u →
      (∀ i j, i ≠ j → ¬G i j → ∀ k,
        1/(grid.width*ε) ≤ |frequency i k-frequency j k|) →
      (∀ S : Finset ι, (∀ i ∈ S, radialShrink (2*ε*c i) (A i) ≠ 0 ∨ i = i₀) →
        (S:Set ι).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) →
      (∀ i : RemainderIndex i₀, ∀ k, |frequency i k-frequency i₀ k| ≤ freqBound) →
      freqBound*(grid.width/(grid.branching:ℝ)^level) ≤ F*θ →
    ∀ (n' : ℝ → ℝ) (c' : ℝ → ι → ℝ) (A' : ℝ → ι → EuclideanSpace ℂ κ)
      (lam' : ℝ → ι → ℂ),
      (∀ b ∈ grid.root, 0 < n' b) → (∀ b ∈ grid.root, ∀ i, 0 < c' b i) →
      (∀ b ∈ grid.root, ∀ i,
        ‖massPowerScale (n' b) (c' b i) (-(1/p)) (phaseMu D p-1+1/p) • A' b i-
          diagonalModulation (frequency i)
            (massPowerScale n (c i) (-(1/p)) (phaseMu D p-1+1/p) • A i) b‖ ≤
          ε*(c i/n)^(1/p)*(c i)^phaseMu D p) →
      (∀ b ∈ grid.root, ∀ i,
        ‖(((n' b)^(phaseMu D p-1):ℝ):ℂ) • (lam' b i • A' b i)-
          ((n^(phaseMu D p-1):ℝ):ℂ) • (lam i • diagonalModulation (frequency i) (A i) b)‖ ≤
          ε*K*(c i/n)) →
      (u < 1/2 → lam i₀ ≠ 0 ∧ 0 ≤ q ∧ q < 1 ∧ q ≤ ε ∧
        0 ≤ (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ∧
        (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ≤ 1 ∧
        1-(c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ≤ 2*u ∧
        (∀ b ∈ grid.root, ‖lam' b i₀-lam i₀‖ ≤ q*‖lam i₀‖) ∧
        (∀ b ∈ grid.root, |(c' b i₀/n' b)^(1-phaseMu D p-1/p)*‖lam' b i₀‖-
          (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖| ≤ 24*ε*u)) →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ b, 0 ≤ Γ b) ∧
        (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ s t, grid.index level s = grid.index level t → Γ s = Γ t) ∧
        ∀ b ∈ grid.root, sourcePredictionValue p (phaseMu D p) (n' b) (c' b) (A' b) (lam' b) ≤
          Real.exp (SourceParameters.step L^(-(1/32:ℝ))*u)*Γ b := by
  filter_upwards [eventually_source_balanced_grid_parameters C F hC hF,
    eventually_source_dominant_grid_parameters C F hC hF] with L hbalanced hdominant
  intro D N hD hN hlog
  dsimp only
  intro ι κ _ _ grid level hlevel G hsym c m n hc hn hm htotal frequency A lam i₀
    Aconst freqBound u q hAconst hfreq hu hpower hsize hA hlam hlamGraph hoff hsep hcard
    hfreqBound hmesh n' c' A' lam' hn' hc' hscaled hnum hdom
  by_cases hb : 1/2 ≤ u
  · exact hbalanced D N hD hN hlog ι κ grid level hlevel G hsym c m n hc hn hm htotal
      frequency A lam i₀ Aconst freqBound u hAconst hfreq hb hpower hsize hA hlam
      hlamGraph hoff hsep hcard hfreqBound hmesh n' c' A' lam' hn' hc' hscaled hnum
  · obtain ⟨hpath,hq0,hq1,hqε,hcoef0,hcoef1,hdrop,hphase,hmove⟩ := hdom (lt_of_not_ge hb)
    exact hdominant D N hD hN hlog ι κ grid level hlevel G hsym c m n hc hn hm htotal
      frequency A lam i₀ Aconst freqBound u q hAconst hfreq hu hpower hsize hA hlam
      hlamGraph hoff hpath hq0 hq1 hqε hcoef0 hcoef1 hdrop hsep hcard hfreqBound hmesh
      n' c' A' lam' hn' hc' hscaled hnum hphase hmove

end LipschitzHilbert

end

end OAI
