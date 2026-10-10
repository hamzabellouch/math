import OAI.Analysis.LipschitzHilbert.Phase.SourceDominantValues
import OAI.Analysis.LipschitzHilbert.Phase.SourcePhaseParameters
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedGrid

namespace OAI

/-! Construct the actual marked-cell factor in the dominant branch, combining
source amplitude comparison with the proved near-uniform graph averaging. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem exists_source_dominant_grid_prediction :
    ∃ Cav L0 : ℝ, 1 ≤ Cav ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (grid : FiniteLineGrid) (level : ℕ), level ≤ grid.depth →
    ∀ (G : ι → ι → Prop), (∀ ⦃i j⦄, G i j → G j i) →
    ∀ (c m : ι → ℝ) (n : ℝ), (∀ i, 0 < c i) → 0 < n →
      (∀ i, orderMass c (closedNeighborhood G i) ≤ m i) →
      (∑ i, c i/n) ≤ 1 →
    ∀ (frequency : ι → κ → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
      (i₀ : ι) (D p K C ε θ freqBound u q : ℝ),
      1 ≤ D → 4 ≤ p → 1 ≤ K → 0 ≤ C → 0 ≤ ε → ε ≤ 1 → 0 ≤ θ → θ ≤ 1 →
      0 ≤ freqBound → 0 ≤ u → n^(phaseMu D p) ≤ K → C*n^(phaseMu D p) ≤ K →
      (∀ i, ‖A i‖ ≤ C*c i) → (∀ i, ‖lam i‖ ≤ 1) →
      (∀ i, ‖lam i‖ ≤ (c i/m i)^phaseMu D p) →
      (∑ i : RemainderIndex i₀, c i/n) ≤ u →
      lam i₀ ≠ 0 → 0 ≤ q → q < 1 → q ≤ ε →
      0 ≤ (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ →
      (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ≤ 1 →
      1-(c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ≤ 2*u →
      Real.exp (24*p*ε*(2*K)) ≤ 2 → 2*24*p*ε*(2*K) ≤ θ →
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
      (∀ b ∈ grid.root, ‖lam' b i₀-lam i₀‖ ≤ q*‖lam i₀‖) →
      (∀ b ∈ grid.root, |(c' b i₀/n' b)^(1-phaseMu D p-1/p)*‖lam' b i₀‖-
        (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖| ≤ 24*ε*u) →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ b, 0 ≤ Γ b) ∧
        (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ s t, grid.index level s = grid.index level t → Γ s = Γ t) ∧
        ∀ b ∈ grid.root, sourcePredictionValue p (phaseMu D p) (n' b) (c' b) (A' b) (lam' b) ≤
          Real.exp (((12*24^2*p^2*(2*K)^2*ε+θ*(p*(2*K)))+
            (4*Cav*SourceParameters.step L^(-(1/16:ℝ))*p*K+
              p*freqBound*K*(grid.width/(grid.branching:ℝ)^level)))*u)*Γ b := by
  obtain ⟨Cav,L0,hCav,hgrid⟩ := exists_source_supported_grid_prediction
  refine ⟨Cav,L0,hCav,?_⟩
  intro L hL ι κ _ _ grid level hlevel G hG c m n hc hn hm htotal frequency A lam
    i₀ D p K C ε θ freqBound u q hD hp hK hC hε hε1 hθ0 hθ1 hfreq hu hpower hsize hA hlam hlamGraph
    hoff hpath hq0 hq1 hqε hC0 hC1 hdrop hsmall habsorb hsep hcard hfreqBound
    n' c' A' lam' hn' hc' hscaled hnum hphase hcmove
  let shrink := fun i => if i = i₀ then A i else radialShrink (2*ε*c i) (A i)
  let X := fun i => (c i)^(phaseMu D p-1) • shrink i
  have hK0 : 0 ≤ K := by linarith
  have hx (i : RemainderIndex i₀) : X i =
      (c i)^(phaseMu D p-1) • radialShrink (2*ε*c i) (A i) := by
    dsimp only [X,shrink]
    rw [ite_eq_right i.property]
  have hcoeffBase := source_snapshot_graph_coefficient_sum hn hε hC hK0 hsize
    (fun i : RemainderIndex i₀ => c i) (fun i => hc i) (fun i => A i) (fun i => lam i)
    (fun i => hA i) (fun i => hlam i) hoff
  have hcoeff : (∑ i : RemainderIndex i₀,
      ‖predictionCoefficients (fun i => c i/n) X lam D p i‖) ≤ K*u := by
    simpa only [predictionCoefficients,hx] using hcoeffBase
  have hcard' (S : Finset ι) (hs : ∀ i ∈ S, X i ≠ 0 ∨ i = i₀)
      (hind : (S:Set ι).Pairwise (fun i j => ¬G i j)) : (S.card:ℝ) ≤ D := by
    apply hcard S _ hind
    intro i hi
    by_cases he : i = i₀
    · exact Or.inr he
    · rcases hs i hi with hx | he'
      · exact Or.inl (fun hz => hx (by simp only [X,shrink,ite_eq_right he,hz,smul_zero]))
      · exact (he he').elim
  obtain ⟨Γ,hmeas,hint,hpos,havg,hcell,hpoint⟩ := hgrid L hL ι κ grid level hlevel G hG c m hc hm
    frequency (fun i => c i/n) X lam i₀ D p K u freqBound θ hD hp hsep hcard'
    (fun i => (div_pos (hc i) hn).le) htotal hlamGraph hK0 hu hfreq hcoeff
    hfreqBound hθ0 hθ1
  refine ⟨Γ,hmeas,hint,hpos,havg,hcell,?_⟩
  intro b hb
  have hsingle : c i₀/n ≤ ∑ i, c i/n :=
    Finset.single_le_sum (fun i _ => (div_pos (hc i) hn).le) (Finset.mem_univ i₀)
  have hcn : c i₀ ≤ n := (div_le_one hn).mp (hsingle.trans htotal)
  have hμ0 : 0 ≤ phaseMu D p := (phaseMu_positive_le hD (by linarith)).1.le
  have hcompare := source_dominant_values_blend hn (hn' b hb) (by linarith : 0 < p) hμ0
    hε hε1 hK hC hpower hsize c (c' b) hc (hc' b hb) i₀ hcn hoff frequency b
    A (A' b) lam (lam' b) hlam hpath hq0 hq1 hqε (hphase b hb) hA
    (hscaled b hb) (hnum b hb) hC0 hC1 hdrop (hcmove b hb) hp hθ0 hθ1 hsmall habsorb
  dsimp only at hcompare
  rw [source_snapshot_graph_identity] at hcompare
  calc
    _ ≤ Real.exp ((12*24^2*p^2*(2*K)^2*ε+θ*(p*(2*K)))*u)*
        ((1-θ)*graphPredictionValue frequency (fun i => c i/n) X lam D p b+θ) := hcompare
    _ ≤ Real.exp ((12*24^2*p^2*(2*K)^2*ε+θ*(p*(2*K)))*u)*
        (Real.exp ((4*Cav*SourceParameters.step L^(-(1/16:ℝ))*p*K+
          p*freqBound*K*(grid.width/(grid.branching:ℝ)^level))*u)*Γ b) :=
      mul_le_mul_of_nonneg_left (hpoint b hb) (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc,← Real.exp_add]; congr 2; ring

end LipschitzHilbert

end

end OAI
