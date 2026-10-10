import Mathlib.Analysis.SpecialFunctions.Log.Base
import OAI.NumberTheory.Catalan.Arithmetic.SmallOddPrimePartition
import OAI.NumberTheory.Catalan.Determinants.RawMinorCoefficientNorm

namespace OAI


noncomputable section

namespace InternalCatalan

open Filter
open scoped Topology

theorem determinantRat_two_adic_valuation_lower (z : ℚ) {N : ℕ} (hN : 0 < N)
    (hd : determinantRat z N ≠ 0) :
    -(505 / 4608 : ℝ) * (n N : ℝ) ^ 2 - 2 * (n N : ℝ) -
        (n N : ℝ) * Real.logb 2 (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) ≤
      (padicValRat 2 (determinantRat z N) : ℝ) := by
  have hd₂ : (determinantRat z N : ℚ_[2]) ≠ 0 := by exact_mod_cast hd
  have hF : 0 < discrepancyNormFactor z :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (one_le_discrepancyNormFactor z)
  have hH : 0 < (H N : ℝ) := by unfold H; positivity
  have hA : 0 < 8 * discrepancyNormFactor z * (H N : ℝ) ^ 2 := by positivity
  have hApow : (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) ^ n N ≠ 0 :=
    ne_of_gt (pow_pos hA _)
  have hE : (2 : ℝ) ^ ((505 / 4608 : ℝ) * (n N : ℝ) ^ 2 + 2 * (n N : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (norm_pos_iff.mpr hd₂) (determinantRat_two_adic_norm_le z hN)
  rw [Padic.norm_eq_zpow_neg_valuation hd₂, Padic.valuation_ratCast] at hl
  simp only [Nat.cast_ofNat] at hl
  rw [← Real.rpow_intCast, Real.logb_rpow (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1),
    Real.logb_mul hApow hE, Real.logb_pow,
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at hl
  simp only [Int.cast_neg] at hl
  linarith only [hl]

theorem tendsto_twoAdic_log_error (z : ℚ) :
    Tendsto (fun N : ℕ =>
      (2 + Real.logb 2 (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2)) / (n N : ℝ))
      atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun N : ℕ => Real.logb 2 (N : ℝ) / (48 * (N : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, add_zero] using
      (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 48 0 1 (by norm_num)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hs := (hi.const_mul
    ((2 + Real.logb 2 (8 * discrepancyNormFactor z * (65 : ℝ) ^ 2)) / 48)).add
      (hl.const_mul 2)
  simp only [mul_zero, add_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hF : 0 < discrepancyNormFactor z :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (one_le_discrepancyNormFactor z)
  have hconst : 8 * discrepancyNormFactor z * (65 : ℝ) ^ 2 ≠ 0 := by positivity
  have hfactor : 8 * discrepancyNormFactor z * (H N : ℝ) ^ 2 =
      (8 * discrepancyNormFactor z * (65 : ℝ) ^ 2) * (N : ℝ) ^ 2 := by
    simp only [H, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hfactor, Real.logb_mul hconst (pow_ne_zero _ hNr), Real.logb_pow]
  simp only [n, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hNr]
  ring

theorem determinantRat_two_adic_eventually_lower (z : ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, determinantRat z N ≠ 0 →
      -(505 / 4608 : ℝ) - ε ≤
        (padicValRat 2 (determinantRat z N) : ℝ) / (n N : ℝ) ^ 2 := by
  have he : ∀ᶠ N : ℕ in atTop,
      (2 + Real.logb 2 (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2)) / (n N : ℝ) < ε :=
    (tendsto_order.mp (tendsto_twoAdic_log_error z)).2 ε hε
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with N heN hN
  intro hd
  have hn : 0 < (n N : ℝ) := by unfold n; positivity
  have herr := mul_le_mul_of_nonneg_left
    (le_of_lt ((div_lt_iff₀ hn).mp heN)) (le_of_lt hn)
  have hv := determinantRat_two_adic_valuation_lower z hN hd
  apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
  nlinarith only [herr, hv]

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Filter
open scoped Topology BigOperators

def largeOddPrimeContribution (z : ℚ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc 0 (H N)).filter
      (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)),
    (padicValRat p (determinantRat z N) : ℝ) * Real.log p

theorem log_abs_determinantRat_place_split_lower (z : ℚ) {N : ℕ}
    (hN : 0 < N) (hz : z.den ≤ H N) (hdet : determinantRat z N ≠ 0) :
    (padicValRat 2 (determinantRat z N) : ℝ) * Real.log 2 +
      smallOddPrimeContribution z N + largeOddPrimeContribution z N ≤
      Real.log |(determinantRat z N : ℝ)| := by
  have h := log_abs_determinantRat_truncated_lower z hN hz hdet
  rw [oddPrimeContribution_split z hN] at h
  simpa only [largeOddPrimeContribution, add_assoc] using h

theorem determinantRat_without_large_primes_eventually_lower (z : ℚ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, determinantRat z N ≠ 0 →
      -(505 / 4608 : ℝ) * Real.log 2 - ε ≤
        (Real.log |(determinantRat z N : ℝ)| - largeOddPrimeContribution z N) /
          (n N : ℝ) ^ 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he2 : 0 < ε / (2 * Real.log 2) := by positivity
  have htwo := determinantRat_two_adic_eventually_lower z he2
  have hsmall := smallOddPrimeContribution_eventually_lower z
    (show 0 < ε / 2 by positivity)
  filter_upwards [htwo, hsmall, eventually_gt_atTop (0 : ℕ),
    eventually_ge_atTop z.den] with N htwoN hsmallN hN hden
  intro hdet
  have hz : z.den ≤ H N := by unfold H; omega
  have hn : 0 < (n N : ℝ) := by unfold n; positivity
  have hn2 : 0 < (n N : ℝ) ^ 2 := sq_pos_of_pos hn
  have ht := mul_le_mul_of_nonneg_right (htwoN hdet) (le_of_lt hlog)
  have herr : ε / (2 * Real.log 2) * Real.log 2 = ε / 2 := by
    field_simp [ne_of_gt hlog]
  have hsplit := div_le_div_of_nonneg_right
    (log_abs_determinantRat_place_split_lower z hN hz hdet) (le_of_lt hn2)
  rw [add_div, add_div] at hsplit
  rw [sub_mul, herr] at ht
  rw [sub_div]
  have heq : (padicValRat 2 (determinantRat z N) : ℝ) * Real.log 2 /
      (n N : ℝ) ^ 2 =
      ((padicValRat 2 (determinantRat z N) : ℝ) / (n N : ℝ) ^ 2) * Real.log 2 := by
    ring
  rw [heq] at hsplit
  linarith

end InternalCatalan

end

end OAI
