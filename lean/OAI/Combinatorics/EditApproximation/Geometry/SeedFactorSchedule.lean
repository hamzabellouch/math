import OAI.Combinatorics.EditApproximation.Refinement.StageWarmup
import OAI.Combinatorics.EditApproximation.Geometry.Parameters
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The literal dyadic factor schedule stops at A<=F. Each active pass
replaces A by 4A/F and uses the integer factor a=A/F. -/

namespace EditApproximation




theorem dyadicSeedExponent_active (f initial pass : ℕ) (hf : 3 ≤ f)
    (hpass : pass < dyadicSeedPassCount f initial) :
    f < dyadicSeedExponent f initial pass := by
  have hd : 0 < f - 2 := by omega
  have hproduct : (f - 2) * pass < initial - f := by
    by_contra hn
    have hle : dyadicSeedPassCount f initial ≤ pass :=
      (ceilDiv_le_iff_le_mul hd).2 (le_of_not_gt hn)
    omega
  unfold dyadicSeedExponent
  rw [Nat.mul_comm] at hproduct
  omega

theorem dyadicSeedExponent_terminal (f initial : ℕ) (hf : 3 ≤ f) :
    dyadicSeedExponent f initial (dyadicSeedPassCount f initial) ≤ f := by
  have hd : 0 < f - 2 := by omega
  have hproduct : initial - f ≤ (f - 2) * dyadicSeedPassCount f initial :=
    (ceilDiv_le_iff_le_mul hd).1 le_rfl
  unfold dyadicSeedExponent
  rw [Nat.mul_comm] at hproduct
  omega

theorem dyadicSeedPassCount_le (f initial : ℕ) (hf : 3 ≤ f) :
    dyadicSeedPassCount f initial ≤ initial / (f - 2) + 1 := by
  have hd : 0 < f - 2 := by omega
  apply (ceilDiv_le_iff_le_mul hd).2
  have hfloor := Nat.lt_mul_div_succ initial hd
  nlinarith only [hfloor, show initial - f ≤ initial from Nat.sub_le _ _]

theorem dyadicSeedPassCount_le_initial (f initial : ℕ) (hf : 3 ≤ f) :
    dyadicSeedPassCount f initial ≤ initial := by
  apply (ceilDiv_le_iff_le_mul (by omega : 0 < f - 2)).2
  exact (Nat.sub_le initial f).trans (Nat.le_mul_of_pos_left _ (by omega : 0 < f - 2))

theorem dyadicSeedExponent_succ (f initial pass : ℕ) :
    dyadicSeedExponent f initial (pass + 1) = dyadicSeedExponent f initial pass - (f - 2) := by
  simp only [dyadicSeedExponent, Nat.add_mul, one_mul, Nat.sub_sub]

theorem dyadicSeedFactor_update (f initial pass : ℕ) (hf : 3 ≤ f)
    (hpass : pass < dyadicSeedPassCount f initial) :
    (2 : ℚ) ^ dyadicSeedExponent f initial (pass + 1) =
      4 * (2 : ℚ) ^ dyadicSeedExponent f initial pass / (2 : ℚ) ^ f := by
  have hactive := dyadicSeedExponent_active f initial pass hf hpass
  have hexponent : dyadicSeedExponent f initial (pass + 1) + f =
      dyadicSeedExponent f initial pass + 2 := by rw [dyadicSeedExponent_succ]; omega
  apply (eq_div_iff (pow_ne_zero f (by norm_num : (2 : ℚ) ≠ 0))).2
  rw [← pow_add, hexponent, pow_add]
  norm_num
  ring

theorem dyadicSeedFactor_integer (f initial pass : ℕ) (hf : 3 ≤ f)
    (hpass : pass < dyadicSeedPassCount f initial) :
    refinementFactor ((2 : ℚ) ^ dyadicSeedExponent f initial pass) (2 ^ f) =
      ((2 ^ (dyadicSeedExponent f initial pass - f) : ℕ) : ℚ) := by
  have hactive := dyadicSeedExponent_active f initial pass hf hpass
  have hquotient : (2 : ℚ) ^ dyadicSeedExponent f initial pass / ((2 ^ f : ℕ) : ℚ) =
      ((2 ^ (dyadicSeedExponent f initial pass - f) : ℕ) : ℚ) := by
    push_cast
    apply (div_eq_iff (pow_ne_zero f (by norm_num : (2 : ℚ) ≠ 0))).2
    rw [← pow_add, Nat.sub_add_cancel hactive.le]
  unfold refinementFactor
  rw [hquotient, max_eq_right]
  exact_mod_cast Nat.one_le_two_pow (n := dyadicSeedExponent f initial pass - f)

theorem dyadicSeedFactor_bound (f initial pass : ℕ) :
    (2 : ℚ) ^ dyadicSeedExponent f initial pass ≤ (2 : ℚ) ^ initial :=
  pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)

theorem dyadicSeedFactor_terminal (f initial : ℕ) (hf : 3 ≤ f) :
    (2 : ℚ) ^ dyadicSeedExponent f initial (dyadicSeedPassCount f initial) ≤ (2 ^ f : ℕ) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (dyadicSeedExponent_terminal f initial hf)

theorem dyadicSeedFactor_terminal_refinement (f initial : ℕ) (hf : 3 ≤ f) :
    refinementFactor ((2 : ℚ) ^ dyadicSeedExponent f initial (dyadicSeedPassCount f initial)) (2 ^ f) = 1 := by
  unfold refinementFactor
  apply max_eq_left
  apply (div_le_one (by positivity : (0 : ℚ) < (2 ^ f : ℕ))).2
  exact dyadicSeedFactor_terminal f initial hf





theorem computedSeed_initial_factor (N : ℕ) :
    (2 : ℚ) ^ computedSeedInitialExponent N =
      ((integerParameters N).initialFactor : ℚ) := by
  simp only [computedSeedInitialExponent, integerParameters, inputHeight, Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_mul, Nat.mul_comm]

theorem computedSeedPassCount_le_height (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) : computedSeedPassCount N ≤ inputHeight N := by
  have hf : 3 ≤ smallLogExponent N := by
    have h := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hell
    omega
  have hlogs := (inputSmallLog_bounds N hN).1
  have hp : coarseExponent (inputSmallLog N) ≤ inputSmallLog N :=
    (Nat.sqrt_le_self _).trans ((Nat.sqrt_le_self _).trans (Nat.log_le_self _ _))
  have hell4 : 4 ≤ inputSmallLog N :=
    (by decide : 4 ≤ (2 : ℕ) ^ 3).trans
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hf)
  have hmul := Nat.mul_le_mul (show coarseExponent (inputSmallLog N) + 4 ≤ 2 * inputSmallLog N by omega) hlogs
  have hsmall : computedSeedInitialExponent N ≤ inputSmallLog N ^ 3 := by
    unfold computedSeedInitialExponent
    apply hmul.trans
    have h := Nat.mul_le_mul_right (inputSmallLog N ^ 2) (by omega : 2 ≤ inputSmallLog N)
    nlinarith only [h]
  have hpoly := inputHeight_polynomial_slack N hN hell
  have hellOne : (1 : ℝ) ≤ inputSmallLog N := by exact_mod_cast (show 1 ≤ inputSmallLog N from (by decide : 1 ≤ (4 : ℕ)).trans hell4)
  have hpower : (inputSmallLog N : ℝ) ^ 3 ≤ (inputSmallLog N : ℝ) ^ 20000 :=
    pow_le_pow_right₀ hellOne (by decide : 3 ≤ 20000)
  have hH : inputSmallLog N ^ 3 ≤ inputHeight N := by exact_mod_cast hpower.trans hpoly
  exact (dyadicSeedPassCount_le_initial _ _ hf).trans (hsmall.trans hH)

end EditApproximation

end OAI
