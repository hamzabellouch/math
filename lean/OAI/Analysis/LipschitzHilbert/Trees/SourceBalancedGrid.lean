import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictionValues
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedGrid

namespace OAI

/-! Construct the actual marked-cell factor in the balanced branch, combining
source amplitude comparison with the proved near-uniform graph averaging. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem exists_source_balanced_grid_prediction :
    ∃ Cav L0 : ℝ, 1 ≤ Cav ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (grid : FiniteLineGrid) (level : ℕ), level ≤ grid.depth →
    ∀ (G : ι → ι → Prop), (∀ ⦃i j⦄, G i j → G j i) →
    ∀ (c m : ι → ℝ) (n : ℝ), (∀ i, 0 < c i) → 0 < n →
      (∀ i, orderMass c (closedNeighborhood G i) ≤ m i) →
      (∑ i, c i/n) ≤ 1 →
    ∀ (frequency : ι → κ → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
      (i₀ : ι) (D p K C ε θ freqBound u : ℝ),
      1 ≤ D → 4 ≤ p → 0 ≤ K → 0 ≤ C → 0 ≤ ε → 0 ≤ θ → θ ≤ 1 →
      0 ≤ freqBound → 1/2 ≤ u → n^(phaseMu D p) ≤ K → C*n^(phaseMu D p) ≤ K →
      (∀ i, ‖A i‖ ≤ C*c i) → (∀ i, ‖lam i‖ ≤ 1) →
      (∀ i, ‖lam i‖ ≤ (c i/m i)^phaseMu D p) →
      (∑ i : RemainderIndex i₀, c i/n) ≤ u →
      (∀ i j, i ≠ j → ¬G i j → ∀ k,
        1/(grid.width*SourceParameters.step L^(-(1/8:ℝ))) ≤
          |frequency i k-frequency j k|) →
      (∀ S : Finset ι, (∀ i ∈ S, radialShrink (2*ε*c i) (A i) ≠ 0 ∨ i = i₀) →
        (S:Set ι).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) →
      (∀ i : RemainderIndex i₀, ∀ k, |frequency i k-frequency i₀ k| ≤ freqBound) →
    ∀ (n' : ℝ → ℝ) (c' : ℝ → ι → ℝ)
      (A' : ℝ → ι → EuclideanSpace ℂ κ) (lam' : ℝ → ι → ℂ),
      (∀ b ∈ grid.root, 0 < n' b) → (∀ b ∈ grid.root, ∀ i, 0 < c' b i) →
      (∀ b ∈ grid.root, ∀ i,
        ‖massPowerScale (n' b) (c' b i) (-(1/p)) (phaseMu D p-1+1/p) • A' b i-
          diagonalModulation (frequency i)
            (massPowerScale n (c i) (-(1/p)) (phaseMu D p-1+1/p) • A i) b‖ ≤
          ε*(c i/n)^(1/p)*(c i)^(phaseMu D p)) →
      (∀ b ∈ grid.root, ∀ i,
        ‖(((n' b)^(phaseMu D p-1):ℝ):ℂ) • (lam' b i • A' b i)-
          ((n^(phaseMu D p-1):ℝ):ℂ) • (lam i • diagonalModulation (frequency i) (A i) b)‖ ≤
          ε*K*(c i/n)) →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ b, 0 ≤ Γ b) ∧
        (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ s t, grid.index level s = grid.index level t → Γ s = Γ t) ∧
        ∀ b ∈ grid.root, sourcePredictionValue p (phaseMu D p) (n' b) (c' b) (A' b) (lam' b) ≤
          Real.exp (((6*p*ε*K+2*θ*(p*K))+
            (4*Cav*SourceParameters.step L^(-(1/16:ℝ))*p*K+
              p*freqBound*K*(grid.width/(grid.branching:ℝ)^level)))*u)*Γ b := by
  obtain ⟨Cav,L0,hCav,hgrid⟩ := exists_source_supported_grid_prediction
  refine ⟨Cav,L0,hCav,?_⟩
  intro L hL ι κ _ _ grid level hlevel G hG c m n hc hn hm htotal frequency A lam
    i₀ D p K C ε θ freqBound u hD hp hK hC hε hθ0 hθ1 hfreq hu hpower hsize hA hlam hlamGraph
    hoff hsep hcard hfreqBound n' c' A' lam' hn' hc' hscaled hnum
  let X := fun i => (c i)^(phaseMu D p-1) • radialShrink (2*ε*c i) (A i)
  have hcoeff : (∑ i : RemainderIndex i₀,
      ‖predictionCoefficients (fun i => c i/n) X lam D p i‖) ≤ K*u :=
    source_snapshot_graph_coefficient_sum hn hε hC hK hsize
      (fun i : RemainderIndex i₀ => c i) (fun i => hc i) (fun i => A i) (fun i => lam i)
      (fun i => hA i) (fun i => hlam i) hoff
  have hcard' (S : Finset ι) (hs : ∀ i ∈ S, X i ≠ 0 ∨ i = i₀)
      (hind : (S:Set ι).Pairwise (fun i j => ¬G i j)) : (S.card:ℝ) ≤ D := by
    apply hcard S _ hind
    intro i hi
    rcases hs i hi with hx | he
    · exact Or.inl (fun hz => hx (by simp only [X,hz,smul_zero]))
    · exact Or.inr he
  obtain ⟨Γ,hmeas,hint,hpos,havg,hcell,hpoint⟩ := hgrid L hL ι κ grid level hlevel G hG c m hc hm
    frequency (fun i => c i/n) X lam i₀ D p K u freqBound θ hD hp hsep hcard'
    (fun i => (div_pos (hc i) hn).le) htotal hlamGraph hK (by linarith) hfreq hcoeff
    hfreqBound hθ0 hθ1
  refine ⟨Γ,hmeas,hint,hpos,havg,hcell,?_⟩
  intro b hb
  have hcompare := source_balanced_values_blend hn (hn' b hb) c (c' b) hc (hc' b hb)
    (by linarith : 1 ≤ p) hε hK hpower hu htotal frequency b A (A' b) lam (lam' b)
    hlam (hscaled b hb) (hnum b hb) hC hsize hA hθ0 hθ1
  rw [source_snapshot_graph_identity] at hcompare
  calc
    _ ≤ Real.exp ((6*p*ε*K+2*θ*(p*K))*u)*
        ((1-θ)*graphPredictionValue frequency (fun i => c i/n) X lam D p b+θ) := hcompare
    _ ≤ Real.exp ((6*p*ε*K+2*θ*(p*K))*u)*
        (Real.exp ((4*Cav*SourceParameters.step L^(-(1/16:ℝ))*p*K+
          p*freqBound*K*(grid.width/(grid.branching:ℝ)^level))*u)*Γ b) :=
      mul_le_mul_of_nonneg_left (hpoint b hb) (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc,← Real.exp_add]; congr 2; ring

end LipschitzHilbert

end

end OAI
