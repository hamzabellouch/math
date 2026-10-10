import OAI.NumberTheory.TwoPoint.Bounds.ComplexBinSummation
import OAI.NumberTheory.TwoPoint.Walks.RetainedFinalScale

namespace OAI

/-! The complex retained graph has an exponentially vanishing normalized contribution. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma exists_fixed_spectral_parameter_ge (C W₀ : ℝ) (hC : 0 ≤ C) :
    ∃ W : ℝ, 10 ≤ W ∧ W₀ ≤ W ∧
      Real.exp 5 * (C / Real.sqrt W) ≤ Real.exp (-1) := by
  obtain ⟨W, hW, hc⟩ := exists_fixed_spectral_parameter C hC
  refine ⟨max W W₀, hW.trans (le_max_left _ _), le_max_right _ _, ?_⟩
  apply le_trans _ hc
  gcongr
  exact le_max_left _ _

lemma exp_neg_nat_exp_lt_two (J : ℕ) (hJ : 1 ≤ J) :
    Real.exp (Real.exp (-(J : ℝ))) < 2 := by
  have hj : Real.exp (-(J : ℝ)) ≤ Real.exp (-1) := by
    apply Real.exp_le_exp.mpr
    exact_mod_cast (show -(J : ℤ) ≤ -1 by omega)
  have hlog : Real.exp (-(J : ℝ)) < Real.log 2 := by
    have := Real.log_two_gt_d9
    have := Real.exp_neg_one_lt_half
    linarith
  calc
    _ < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hlog
    _ = _ := Real.exp_log (by norm_num)

theorem ModFiveThetaInput.eventually_canonical_complex_saving
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ (W : ℝ) (hW : 10 ≤ W),
      Real.exp 5 * ((2 * Real.exp 150) / Real.sqrt W) ≤ Real.exp (-1) →
      ∀ (h : ℕ) (_hh : 0 < h) (E : Finset ℕ)
        (hE : ∀ p, p.Prime → p ∣ h → p ∈ E),
      ∀ᶠ L : ℝ in atTop, ∀ hL : 1 ≤ L,
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
      ‖∑ j ∈ bins, v j * canonicalComplexPrefix h E W L (eligible j) hL
        (by linarith) hE F G (N j)‖ /
          totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η ≤
        (80 * (1212 * Real.exp 1 + 606)) * Real.exp (-(J : ℝ)) := by
  obtain ⟨A, hA, hb⟩ := hprime.eventually_canonical_complex_bin_sum hBr
  refine ⟨A, hA, ?_⟩
  intro W hW hchoice h hh E hE
  have hWone : 1 ≤ W := by linarith
  filter_upwards [hb h hh E hE W hWone, eventually_bin_error_saving W hWone,
    eventually_primeSupplyCount_pos W (by linarith), eventually_ge_atTop (1 : ℝ)]
    with L hb herr hJ hL
  intro hL'
  dsimp only
  let J := primeSupplyCount W L
  let η := Real.exp (-(J : ℝ))
  have hη : 0 < η := Real.exp_pos _
  have hηone : η ≤ 1 := Real.exp_le_one_iff.mpr (by
    dsimp only [J]
    exact neg_nonpos.mpr (Nat.cast_nonneg _))
  have hηtwo : Real.exp η < 2 := exp_neg_nat_exp_lt_two J hJ
  intro eligible he hpos hbin F G hF hG N v hN hv
  have hbound := hb hL' η hη hηone hηtwo (paddingBinIndices L η) eligible he hpos hbin
    F G hF hG N v hN hv
  have hs := retained_spectral_scale L W J 1 (paddingBinIndices L η).card (by linarith)
    (by linarith) (Nat.cast_nonneg _) (paddingBinIndices_card_linear L η hL hη hηone)
    hchoice herr
  simp only [Nat.cast_one, one_pow, mul_one] at hs
  apply hbound.trans
  calc
    _ = 80 * ((6 * (paddingBinIndices L η).card / L) *
        ((Real.exp 1 * (2 * (Real.exp (4 * J) *
          (2 * Real.exp 150 * Real.sqrt W) ^ J))) / W ^ J) +
        6 * (paddingBinIndices L η).card * Real.exp (-L)) := by ring
    _ ≤ 80 * ((1212 * Real.exp 1 + 606) * Real.exp (-(J : ℝ))) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by ring

end TwoPointCorrelations

end OAI
