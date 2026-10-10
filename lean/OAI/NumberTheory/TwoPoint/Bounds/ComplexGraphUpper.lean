import OAI.NumberTheory.TwoPoint.Bounds.ComplexFinalScale
import OAI.NumberTheory.TwoPoint.Bounds.ComplexCanonicalDeletion
import OAI.NumberTheory.TwoPoint.Bounds.FinalCorrelationBound

namespace OAI

/-! The complete uncut complex graph is small: the retained graph and the
two endpoint deletion errors share the same exponential saving. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem complex_graph_fixed_scale (hP : ModFiveThetaInput)
    (hBr : BravermanDepth22Input) :
    ∃ (A : ℕ) (W : ℝ), 1000 ≤ A ∧ 10 ≤ W ∧
      ∀ (h : ℕ), 0 < h → ∀ (E : Finset ℕ)
        (_hE : ∀ p, p.Prime → p ∣ h → p ∈ E),
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop, ∀ _hL : 1 ≤ L,
      let J := primeSupplyCount W L
      let η := Real.exp (-(J : ℝ))
      let bins := paddingBinIndices L η
      ∀ eligible : ℤ → ℕ → ℕ → Prop,
        (∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q) →
        (∀ j ∈ bins, ∀ d q, eligible j d q → 0 < d ∧ 0 < q) →
        (∀ j ∈ bins, ∀ d q, eligible j d q → actualPaddingBin η (Real.log d) j q) →
      ∀ (F G : ℤ → ℂ), (∀ n, ‖F n‖ ≤ 1) → (∀ n, ‖G n‖ ≤ 1) →
      ∀ (N : ℤ → ℕ) (v : ℤ → ℂ),
        (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
        (∀ j ∈ bins, ‖v j‖ ≤ 1) →
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      ‖∑ j ∈ bins, v j * canonicalComplexUncutPrefix h E W L (eligible j) F G (N j)‖ /
        totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η ≤
          C * η := by
  obtain ⟨As, hAs, hs⟩ := hP.eventually_canonical_complex_saving hBr
  obtain ⟨Ad, hAd, hd⟩ := hBr.eventually_canonical_shifted_source_deletion_uniform hP
  obtain ⟨W, hW, hchoice⟩ := exists_fixed_spectral_parameter (2 * Real.exp 150) (by positivity)
  let A := As + Ad
  have hA : 1000 ≤ A := by dsimp only [A]; omega
  have hWone : 1 ≤ W := by linarith
  refine ⟨A, W, hA, hW, ?_⟩
  intro h hh E hE
  obtain ⟨Cd, hCd, hd⟩ := hd h E hE W 3 hW (by norm_num)
  let Cs : ℝ := 80 * (1212 * Real.exp 1 + 606)
  refine ⟨Cs + 4 * (Cd + 4), by dsimp only [Cs]; positivity, ?_⟩
  filter_upwards [hs W hW hchoice h hh E hE, hd,
    hP.eventually_canonical_retained_mass E W hWone,
    eventually_rare_error_saving W hWone, eventually_ge_atTop (101 : ℝ)]
      with L hs hd hm hr hlarge
  intro hL
  dsimp only
  let J := primeSupplyCount W L
  let η := Real.exp (-(J : ℝ))
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let M := paddingTiltNormalizer Q * ∏ j, primeHarmonicMass (P j)
  let S₀ := totalPaddingBinMass (primeTupleDivisors P) Q L η
  let bins := paddingBinIndices L η
  have hη : 0 < η := Real.exp_pos _
  have hηone : η ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg J))
  intro eligible he hpos hbin F G hF hG N v hN hv
  have hN' (A' : ℕ) (hA' : A' ≤ A) (j : ℤ) (hj : j ∈ bins) :
      Real.exp (L ^ A' / 2) ≤ (N j : ℝ) :=
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ hL hA') (by norm_num))).trans (hN j hj)
  have hmass := hm hL η hη
  have hV : 1 ≤ ∏ j, primeHarmonicMass (P j) := (one_le_pow₀ hWone).trans hmass.1
  have hM : 0 < M := mul_pos (paddingTiltNormalizer_pos Q) (by linarith)
  have hmS : M / 2 ≤ S₀ := hmass.2
  have hS₀ : 0 < S₀ := (half_pos hM).trans_le hmS
  let raw := ∑ j ∈ bins, v j * canonicalComplexUncutPrefix h E W L (eligible j) F G (N j)
  let retained := ∑ j ∈ bins,
    v j * canonicalComplexPrefix h E W L (eligible j) hL hWone hE F G (N j)
  let cost := fun site => canonicalShiftedSourceDeletion h E W L η (Real.exp (4 * J))
    hL hWone hE bins (fun d => Real.log d) eligible site (fun _ => 1) N
  have hret : ‖retained‖ / S₀ ≤ Cs * η :=
    hs hL eligible he hpos hbin F G hF hG N v (hN' As (by dsimp only [A]; omega)) hv
  have hdelete : ‖raw - retained‖ ≤ cost (fun _ _ _ => 0) +
      cost (fun _ d q => (h * q * d : ℕ)) :=
    canonical_complex_weighted_correlation_deletion h E W L η hL hWone hE bins
      (fun d => Real.log d) eligible N v F G hF hG hbin hv
  have hc (site : ℤ → ℕ → ℕ → ℤ) : cost site / M ≤ (Cd + 4) * η := by
    have hx := hd hL η (Real.exp (4 * J)) hη hηone (Real.exp_pos _) bins
      (fun d => Real.log d) eligible
      (paddingBinIndices_card_polynomial L W hlarge hWone) he hbin site (fun _ => 1) N
      (hN' Ad (by dsimp only [A]; omega))
    exact hx.trans (quantitative_deletion_small L W Cd J hL hWone hCd.le
      (primeSupplyCount_final_budget L W hL hWone) hr)
  have hdel : ‖raw - retained‖ ≤ 2 * M * ((Cd + 4) * η) := by
    have h₁ := (div_le_iff₀ hM).mp (hc (fun _ _ _ => 0))
    have h₂ := (div_le_iff₀ hM).mp (hc (fun _ d q => (h * q * d : ℕ)))
    nlinarith
  have hrbound := (div_le_iff₀ hS₀).mp hret
  have hmb := mul_le_mul_of_nonneg_right (show M ≤ 2 * S₀ by linarith)
    (show 0 ≤ 2 * ((Cd + 4) * η) by positivity)
  apply (div_le_iff₀ hS₀).mpr
  have htri : ‖raw‖ ≤ ‖raw - retained‖ + ‖retained‖ := by
    simpa only [sub_add_cancel] using norm_add_le (raw - retained) retained
  change ‖raw‖ ≤ _
  nlinarith

end TwoPointCorrelations

end OAI
