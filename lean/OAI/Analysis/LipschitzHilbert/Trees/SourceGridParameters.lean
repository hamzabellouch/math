import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictionParameters
import OAI.Analysis.LipschitzHilbert.Trees.SourceBalancedGrid
import OAI.Analysis.LipschitzHilbert.Phase.SourceDominantGrid

namespace OAI

/-! The source prediction scale gives one uniform marked-cell error in
both branches. The only mesh hypothesis is the explicit carrier oscillation
bound on a cell; the averaging measure and its remainder are already proved. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

private theorem source_grid_cost_le {p K θ Cav F freq mesh A R : ℝ}
    (hp : 0 ≤ p) (hK : 0 ≤ K) (hmesh : freq*mesh ≤ F*θ)
    (hbudget : A+(4*Cav+F)*θ*p*K ≤ R) :
    A+(4*Cav*θ*p*K+p*freq*K*mesh) ≤ R := by
  have hm := mul_le_mul_of_nonneg_left hmesh (mul_nonneg hp hK)
  calc
    _ = A+4*Cav*θ*p*K+(p*K)*(freq*mesh) := by ring
    _ ≤ A+4*Cav*θ*p*K+(p*K)*(F*θ) := add_le_add le_rfl hm
    _ = A+(4*Cav+F)*θ*p*K := by ring
    _ ≤ R := hbudget

/-- The balanced source factor has a normalized, measurable cell-constant
majorant with pointwise error `G^(-1/32) * u` at the actual parameters. -/
theorem eventually_source_balanced_grid_parameters (C F : ℝ)
    (hC : 0 ≤ C) (hF : 0 ≤ F) :
    ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ,
      1 ≤ D → 0 < N → Real.log N ≤ 2*L →
      let p := Real.sqrt L
      let K := L^C*(1+N^phaseMu D p)
      let Gstep := SourceParameters.step L
      let ε := Gstep^(-(1/8:ℝ))
      let θ := Gstep^(-(1/16:ℝ))
      ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
        (grid : FiniteLineGrid) (level : ℕ), level ≤ grid.depth →
      ∀ (G : ι → ι → Prop), (∀ ⦃i j⦄, G i j → G j i) →
      ∀ (c m : ι → ℝ) (n : ℝ), (∀ i, 0 < c i) → 0 < n →
        (∀ i, orderMass c (closedNeighborhood G i) ≤ m i) →
        (∑ i, c i/n) ≤ 1 →
      ∀ (frequency : ι → κ → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
        (i₀ : ι) (Aconst freqBound u : ℝ),
        0 ≤ Aconst → 0 ≤ freqBound → 1/2 ≤ u →
        n^(phaseMu D p) ≤ K → Aconst*n^(phaseMu D p) ≤ K →
        (∀ i, ‖A i‖ ≤ Aconst*c i) → (∀ i, ‖lam i‖ ≤ 1) →
        (∀ i, ‖lam i‖ ≤ (c i/m i)^phaseMu D p) →
        (∑ i : RemainderIndex i₀, c i/n) ≤ u →
        (∀ i j, i ≠ j → ¬G i j → ∀ k,
          1/(grid.width*ε) ≤ |frequency i k-frequency j k|) →
        (∀ S : Finset ι,
          (∀ i ∈ S, radialShrink (2*ε*c i) (A i) ≠ 0 ∨ i = i₀) →
          (S:Set ι).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) →
        (∀ i : RemainderIndex i₀, ∀ k, |frequency i k-frequency i₀ k| ≤ freqBound) →
        freqBound*(grid.width/(grid.branching:ℝ)^level) ≤ F*θ →
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
            Real.exp ((Gstep^(-(1/32:ℝ)))*u)*Γ b := by
  obtain ⟨Cav,L0,hCav,hgrid⟩ := exists_source_balanced_grid_prediction
  have hparams := eventually_source_prediction_parameters C (4*Cav+F) hC (by linarith)
  filter_upwards [hparams,eventually_ge_atTop L0,eventually_ge_atTop (16:ℝ)]
    with L hparams hL hL16
  intro D N hD hN hlog
  dsimp only
  let p := Real.sqrt L
  let K := L^C*(1+N^phaseMu D p)
  let ε := SourceParameters.step L^(-(1/8:ℝ))
  let θ := SourceParameters.step L^(-(1/16:ℝ))
  have hp : 4 ≤ p := by
    dsimp [p]
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    norm_num
    exact hL16
  have hK : 1 ≤ K := by
    have hpow : 1 ≤ L^C := Real.one_le_rpow (by linarith) hC
    have hmass : 0 ≤ N^phaseMu D p := Real.rpow_nonneg hN.le _
    exact one_le_mul_of_one_le_of_one_le hpow (by linarith)
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have hε : 0 ≤ ε := Real.rpow_nonneg (le_trans zero_le_one hG) _
  have hθ : 0 ≤ θ := Real.rpow_nonneg (le_trans zero_le_one hG) _
  have hθ1 : θ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num)
  have hbudget := (hparams D N hD hN hlog).2.2
  change (12*24^2*p^2*(2*K)^2*ε+θ*(p*(2*K)))+
    (4*Cav+F)*θ*p*K ≤ SourceParameters.step L^(-(1/32:ℝ)) at hbudget
  intro ι κ _ _ grid level hlevel G hsym c m n hc hn hm htotal frequency A lam i₀
    Aconst freqBound u hAconst hfreq hu hpower hsize hA hlam hlamGraph hoff
    hsep hcard hfreqBound hmesh n' c' A' lam' hn' hc' hscaled hnum
  obtain ⟨Γ,hmeas,hint,hpos,havg,hcell,hpoint⟩ := hgrid L hL ι κ grid level hlevel G hsym
    c m n hc hn hm htotal frequency A lam i₀ D p K Aconst ε θ freqBound u
    hD hp (by linarith) hAconst hε hθ hθ1 hfreq hu hpower hsize hA hlam hlamGraph
    hoff hsep hcard hfreqBound n' c' A' lam' hn' hc' hscaled hnum
  refine ⟨Γ,hmeas,hint,hpos,havg,hcell,?_⟩
  have hcost := source_grid_cost_le (show 0 ≤ p by linarith) (show 0 ≤ K by linarith)
    hmesh ((add_le_add
      (balanced_prediction_cost_le_dominant (by linarith : 1 ≤ p) hK hε) le_rfl).trans hbudget)
  intro b hb
  exact (hpoint b hb).trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcost (by linarith))) (hpos b))

/-- The unshrunk path vector in the dominant branch has the same final
marked-cell error as the balanced branch. All phase and mass hypotheses
remain the explicit local estimates proved for the original packets. -/
theorem eventually_source_dominant_grid_parameters (C F : ℝ)
    (hC : 0 ≤ C) (hF : 0 ≤ F) :
    ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ,
      1 ≤ D → 0 < N → Real.log N ≤ 2*L →
      let p := Real.sqrt L
      let K := L^C*(1+N^phaseMu D p)
      let Gstep := SourceParameters.step L
      let ε := Gstep^(-(1/8:ℝ))
      let θ := Gstep^(-(1/16:ℝ))
      ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
        (grid : FiniteLineGrid) (level : ℕ), level ≤ grid.depth →
      ∀ (G : ι → ι → Prop), (∀ ⦃i j⦄, G i j → G j i) →
      ∀ (c m : ι → ℝ) (n : ℝ), (∀ i, 0 < c i) → 0 < n →
        (∀ i, orderMass c (closedNeighborhood G i) ≤ m i) →
        (∑ i, c i/n) ≤ 1 →
      ∀ (frequency : ι → κ → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
        (i₀ : ι) (Aconst freqBound u q : ℝ),
        0 ≤ Aconst → 0 ≤ freqBound → 0 ≤ u →
        n^(phaseMu D p) ≤ K → Aconst*n^(phaseMu D p) ≤ K →
        (∀ i, ‖A i‖ ≤ Aconst*c i) → (∀ i, ‖lam i‖ ≤ 1) →
        (∀ i, ‖lam i‖ ≤ (c i/m i)^phaseMu D p) →
        (∑ i : RemainderIndex i₀, c i/n) ≤ u →
        lam i₀ ≠ 0 → 0 ≤ q → q < 1 → q ≤ ε →
        0 ≤ (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ →
        (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ≤ 1 →
        1-(c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ≤ 2*u →
        (∀ i j, i ≠ j → ¬G i j → ∀ k,
          1/(grid.width*ε) ≤ |frequency i k-frequency j k|) →
        (∀ S : Finset ι,
          (∀ i ∈ S, radialShrink (2*ε*c i) (A i) ≠ 0 ∨ i = i₀) →
          (S:Set ι).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) →
        (∀ i : RemainderIndex i₀, ∀ k, |frequency i k-frequency i₀ k| ≤ freqBound) →
        freqBound*(grid.width/(grid.branching:ℝ)^level) ≤ F*θ →
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
            Real.exp ((Gstep^(-(1/32:ℝ)))*u)*Γ b := by
  obtain ⟨Cav,L0,hCav,hgrid⟩ := exists_source_dominant_grid_prediction
  have hparams := eventually_source_prediction_parameters C (4*Cav+F) hC (by linarith)
  filter_upwards [hparams,eventually_ge_atTop L0,eventually_ge_atTop (16:ℝ)]
    with L hparams hL hL16
  intro D N hD hN hlog
  dsimp only
  let p := Real.sqrt L
  let K := L^C*(1+N^phaseMu D p)
  let ε := SourceParameters.step L^(-(1/8:ℝ))
  let θ := SourceParameters.step L^(-(1/16:ℝ))
  have hp : 4 ≤ p := by
    dsimp [p]
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    norm_num
    exact hL16
  have hK : 1 ≤ K := by
    have hpow : 1 ≤ L^C := Real.one_le_rpow (by linarith) hC
    have hmass : 0 ≤ N^phaseMu D p := Real.rpow_nonneg hN.le _
    exact one_le_mul_of_one_le_of_one_le hpow (by linarith)
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have hε : 0 ≤ ε := Real.rpow_nonneg (le_trans zero_le_one hG) _
  have hε1 : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num)
  have hθ : 0 ≤ θ := Real.rpow_nonneg (le_trans zero_le_one hG) _
  have hθ1 : θ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num)
  obtain ⟨hexp,habsorb,hbudget⟩ := hparams D N hD hN hlog
  change (12*24^2*p^2*(2*K)^2*ε+θ*(p*(2*K)))+
    (4*Cav+F)*θ*p*K ≤ SourceParameters.step L^(-(1/32:ℝ)) at hbudget
  intro ι κ _ _ grid level hlevel G hsym c m n hc hn hm htotal frequency A lam i₀
    Aconst freqBound u q hAconst hfreq hu hpower hsize hA hlam hlamGraph hoff
    hpath hq0 hq1 hqε hcoeff0 hcoeff1 hdrop hsep hcard hfreqBound hmesh
    n' c' A' lam' hn' hc' hscaled hnum hphase hcmove
  obtain ⟨Γ,hmeas,hint,hpos,havg,hcell,hpoint⟩ := hgrid L hL ι κ grid level hlevel G hsym
    c m n hc hn hm htotal frequency A lam i₀ D p K Aconst ε θ freqBound u q
    hD hp hK hAconst hε hε1 hθ hθ1 hfreq hu hpower hsize hA hlam hlamGraph
    hoff hpath hq0 hq1 hqε hcoeff0 hcoeff1 hdrop hexp habsorb hsep hcard hfreqBound
    n' c' A' lam' hn' hc' hscaled hnum hphase hcmove
  refine ⟨Γ,hmeas,hint,hpos,havg,hcell,?_⟩
  have hcost := source_grid_cost_le (show 0 ≤ p by linarith) (show 0 ≤ K by linarith)
    hmesh hbudget
  intro b hb
  exact (hpoint b hb).trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcost hu)) (hpos b))

end LipschitzHilbert

end

end OAI
