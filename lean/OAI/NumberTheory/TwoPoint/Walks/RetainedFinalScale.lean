import OAI.NumberTheory.TwoPoint.Bounds.WeightedRetainedBins
import OAI.NumberTheory.TwoPoint.Bounds.PaddingBinCount
import OAI.NumberTheory.TwoPoint.Bounds.FinalErrorScale

namespace OAI

/-! The retained graph contribution at the final fixed parameter choice.
The interval exponent is chosen before all affine coefficients. -/

namespace TwoPointCorrelations

open Filter
open scoped Classical

lemma retained_spectral_scale (L W : ℝ) (J : ℕ) (l : ℕ) (B : ℝ)
    (hL : 0 < L) (hW : 0 < W) (_hB : 0 ≤ B)
    (hbins : B ≤ 101 * L / Real.exp (-(J : ℝ)))
    (hchoice : Real.exp 5 * ((2 * Real.exp 150) / Real.sqrt W) ≤ Real.exp (-1))
    (herr : L / Real.exp (-(J : ℝ)) * Real.exp (-L) ≤ Real.exp (-(J : ℝ))) :
    (6 * B * (l : ℝ) ^ 2 / L) *
      ((Real.exp 1 * (2 * (Real.exp (4 * J) *
        (2 * Real.exp 150 * Real.sqrt W) ^ J))) / W ^ J) +
      6 * B * Real.exp (-L) ≤
        (1212 * Real.exp 1 * (l : ℝ) ^ 2 + 606) * Real.exp (-(J : ℝ)) := by
  have hs : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  have hratio : (2 * Real.exp 150 * Real.sqrt W) / W =
      (2 * Real.exp 150) / Real.sqrt W := by
    apply (div_eq_div_iff hW.ne' hs.ne').mpr
    rw [mul_assoc, ← pow_two, Real.sq_sqrt hW.le]
  have hspec := quantitative_spectral_term (2 * Real.exp 150) W J (by positivity) hW hchoice
  have hmain : (6 * B * (l : ℝ) ^ 2 / L) *
      ((Real.exp 1 * (2 * (Real.exp (4 * J) *
        (2 * Real.exp 150 * Real.sqrt W) ^ J))) / W ^ J) ≤
      1212 * Real.exp 1 * (l : ℝ) ^ 2 * Real.exp (-(J : ℝ)) := by
    calc
      _ ≤ (6 * (101 * L / Real.exp (-(J : ℝ))) * (l : ℝ) ^ 2 / L) *
          ((Real.exp 1 * (2 * (Real.exp (4 * J) *
            (2 * Real.exp 150 * Real.sqrt W) ^ J))) / W ^ J) := by
        gcongr
      _ = (1212 * Real.exp 1 * (l : ℝ) ^ 2) *
          (Real.exp (5 * J) * ((2 * Real.exp 150) / Real.sqrt W) ^ J) := by
        have he : Real.exp (5 * (J : ℝ)) =
            Real.exp (4 * J) * Real.exp (J : ℝ) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hr : (Real.exp 1 * (2 * (Real.exp (4 * J) *
            (2 * Real.exp 150 * Real.sqrt W) ^ J))) / W ^ J =
            2 * Real.exp 1 * Real.exp (4 * J) *
              ((2 * Real.exp 150) / Real.sqrt W) ^ J := by
          calc
            _ = (2 * Real.exp 1 * Real.exp (4 * J)) *
                ((2 * Real.exp 150 * Real.sqrt W) ^ J / W ^ J) := by ring
            _ = _ := by rw [← div_pow, hratio]
        rw [hr, he, Real.exp_neg]
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hspec (by positivity)
  have herror : 6 * B * Real.exp (-L) ≤ 606 * Real.exp (-(J : ℝ)) := by
    calc
      _ ≤ 6 * (101 * L / Real.exp (-(J : ℝ))) * Real.exp (-L) := by gcongr
      _ = 606 * (L / Real.exp (-(J : ℝ)) * Real.exp (-L)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left herr (by norm_num)
  nlinarith

theorem ModFiveThetaInput.eventually_canonical_retained_saving
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ (A : ℕ) (W : ℝ), 1000 ≤ A ∧ ∃ hW : 10 ≤ W,
      ∀ (h l : ℕ) (_hh : 0 < h) (_hl : 0 < l) (E : Finset ℕ)
        (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
        (_hEl : ∀ p, p.Prime → p ∣ l → p ∈ E),
      ∀ᶠ L : ℝ in atTop, ∀ hL : 1 ≤ L,
      let J := primeSupplyCount W L
      let η := Real.exp (-(J : ℝ))
      let bins := paddingBinIndices L η
      ∀ eligible : ℤ → ℕ → ℕ → Prop,
        (∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q) →
      ∀ (b : ℕ) (N : ℤ → ℕ),
        (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      ‖∑ j ∈ bins, canonicalRetainedPrefix h l b E W L (eligible j) hL
        (by linarith) hE (N j)‖ /
          totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η ≤
        (1212 * Real.exp 1 * (l : ℝ) ^ 2 + 606) * Real.exp (-(J : ℝ)) := by
  obtain ⟨A, hA, hb⟩ := hprime.eventually_canonical_bin_sum_uniform hBr
  obtain ⟨W, hW, hchoice⟩ := exists_fixed_spectral_parameter (2 * Real.exp 150) (by positivity)
  refine ⟨A, W, hA, hW, ?_⟩
  intro h l hh hl E hE hEl
  have hWone : 1 ≤ W := by linarith
  filter_upwards [hb h l hh hl E hE hEl W hWone, eventually_bin_error_saving W hWone,
    eventually_ge_atTop (1 : ℝ)] with L hb herr hL
  intro hL'
  dsimp only
  intro eligible he b N hN
  let J := primeSupplyCount W L
  let η := Real.exp (-(J : ℝ))
  have hη : 0 < η := Real.exp_pos _
  have hηone : η ≤ 1 := Real.exp_le_one_iff.mpr (by
    dsimp only [J]
    exact neg_nonpos.mpr (Nat.cast_nonneg _))
  have hbound := hb hL' η hη hηone (paddingBinIndices L η) eligible he b N hN
  apply hbound.trans
  exact retained_spectral_scale L W J l (paddingBinIndices L η).card (by linarith)
    (by linarith) (Nat.cast_nonneg _) (paddingBinIndices_card_linear L η hL hη hηone)
    hchoice herr

theorem ModFiveThetaInput.eventually_canonical_retained_weighted_saving
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ (A : ℕ) (W : ℝ), 1000 ≤ A ∧ ∃ hW : 10 ≤ W,
      ∀ (h l : ℕ) (_hh : 0 < h) (_hl : 0 < l) (E : Finset ℕ)
        (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
        (_hEl : ∀ p, p.Prime → p ∣ l → p ∈ E),
      ∀ᶠ L : ℝ in atTop, ∀ hL : 1 ≤ L,
      let J := primeSupplyCount W L
      let η := Real.exp (-(J : ℝ))
      let bins := paddingBinIndices L η
      ∀ eligible : ℤ → ℕ → ℕ → Prop,
        (∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q) →
      ∀ (b : ℕ) (N : ℤ → ℕ) (v : ℤ → ℂ),
        (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
      (∀ j ∈ bins, ‖v j‖ ≤ 1) →
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      ‖∑ j ∈ bins, v j * canonicalRetainedPrefix h l b E W L (eligible j) hL
        (by linarith) hE (N j)‖ /
          totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η ≤
        (1212 * Real.exp 1 * (l : ℝ) ^ 2 + 606) * Real.exp (-(J : ℝ)) := by
  obtain ⟨A, hA, hb⟩ := hprime.eventually_canonical_weighted_bin_sum_uniform hBr
  obtain ⟨W, hW, hchoice⟩ := exists_fixed_spectral_parameter (2 * Real.exp 150) (by positivity)
  refine ⟨A, W, hA, hW, ?_⟩
  intro h l hh hl E hE hEl
  have hWone : 1 ≤ W := by linarith
  filter_upwards [hb h l hh hl E hE hEl W hWone, eventually_bin_error_saving W hWone,
    eventually_ge_atTop (1 : ℝ)] with L hb herr hL
  intro hL'
  dsimp only
  intro eligible he b N v hN hv
  let J := primeSupplyCount W L
  let η := Real.exp (-(J : ℝ))
  have hη : 0 < η := Real.exp_pos _
  have hηone : η ≤ 1 := Real.exp_le_one_iff.mpr (by
    dsimp only [J]
    exact neg_nonpos.mpr (Nat.cast_nonneg _))
  have hbound := hb hL' η hη hηone (paddingBinIndices L η) eligible he b N v hN hv
  apply hbound.trans
  exact retained_spectral_scale L W J l (paddingBinIndices L η).card (by linarith)
    (by linarith) (Nat.cast_nonneg _) (paddingBinIndices_card_linear L η hL hη hηone)
    hchoice herr

end TwoPointCorrelations

end OAI
