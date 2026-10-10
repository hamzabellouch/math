import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationHistoryCoupling

namespace OAI

/-! # The bounded sampler's unconditional loss on the main input guard -/

noncomputable section

namespace LowSpaceSubsetSum

private theorem sampler_linear_le_pow {n : ℕ} (hn : 16 ≤ n) : 50 * n + 6 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    omega

private theorem sampler_prime_tail {n : ℕ} (hn : 16 ≤ n) :
    Real.exp (-((n : ℝ) ^ 2 / 4)) ≤ 1 / (2 : ℝ) ^ (2 * n) := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ (2 * n) ≤ Real.exp ((n : ℝ) ^ 2 / 4) := by
    calc
      _ ≤ (Real.exp 1) ^ (2 * n) := pow_le_pow_left₀ (by norm_num) htwo _
      _ = Real.exp ((2 * n : ℕ) : ℝ) := by rw [← Real.exp_nat_mul]; simp
      _ ≤ _ := Real.exp_le_exp.mpr (by push_cast; nlinarith)
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hp

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem rangeCallBound_le (hn : 16 ≤ n) : R.rangeCallBound ≤ 2 ^ (2 * n) := by
  have hm : mixerSize n ≤ n := by
    have h := Finset.card_le_univ (R.mixers 0)
    simpa only [R.card, Fintype.card_fin] using h
  have hg : 2 * blockHalf n 0 ≤ n := by
    simp only [blockHalf, Matrix.cons_val_zero, mixerSize] at *
    omega
  have hp : 2 ^ (2 * blockHalf n 0) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hg
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hterm : 44 * (2 * blockHalf n 0) * 2 ^ (2 * blockHalf n 0) ≤ 44 * n * 2 ^ n :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 44 hg) hp
  have hsmall : 4 * n + 6 ≤ (4 * n + 6) * 2 ^ n := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4 * n + 6) hpow
  have hlinear := sampler_linear_le_pow hn
  unfold rangeCallBound
  calc
    _ ≤ (50 * n + 6) * 2 ^ n := by nlinarith
    _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul_right _ hlinear
    _ = 2 ^ (2 * n) := by rw [← pow_add]; congr 1; omega

theorem samplerError_le_pow (hn : 10000 ≤ n) :
    R.rangeCallBound / (2 : ℝ) ^ (n ^ 3) + 4 * Real.exp (-((n : ℝ) ^ 2 / 4)) ≤
      1 / (2 : ℝ) ^ n := by
  have hcalls : (R.rangeCallBound : ℝ) ≤ (2 : ℝ) ^ (2 * n) := by
    exact_mod_cast R.rangeCallBound_le (by omega)
  have hcube : 4 * n ≤ n ^ 3 := by
    have hsq : 4 ≤ n ^ 2 := by nlinarith [show 16 ≤ n by omega]
    calc
      4 * n ≤ n ^ 2 * n := Nat.mul_le_mul_right n hsq
      _ = n ^ 3 := by ring
  have hrange : R.rangeCallBound / (2 : ℝ) ^ (n ^ 3) ≤ 1 / (2 : ℝ) ^ (2 * n) := by
    apply (div_le_div_of_nonneg_right hcalls (by positivity)).trans
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [one_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hprime := sampler_prime_tail (by omega : 16 ≤ n)
  have hfive : (5 : ℝ) ≤ (2 : ℝ) ^ n := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 3 ≤ n)
    norm_num at h ⊢
    linarith
  calc
    _ ≤ 5 / (2 : ℝ) ^ (2 * n) := by
      simp only [div_eq_mul_inv, one_mul] at hrange hprime ⊢
      linarith
    _ ≤ 1 / (2 : ℝ) ^ n := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      rw [one_mul, two_mul, pow_add]
      exact mul_le_mul_of_nonneg_right hfive (by positivity)

theorem bucketHistoryCoupling_failure_pow (hn : 10000 ≤ n) :
    (R.bucketHistoryCoupling hn).failure ≤ 1 / (2 : ℝ) ^ n :=
  (R.bucketHistoryCoupling_failure hn).trans (R.samplerError_le_pow hn)

/-- The implementation guard makes the coupling error smaller than the
polynomial survival margin, without conditioning on sampling success. -/
theorem samplerError_guard (hn : 10000 ≤ n)
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000) :
    R.rangeCallBound / (2 : ℝ) ^ (n ^ 3) + 4 * Real.exp (-((n : ℝ) ^ 2 / 4)) ≤
      (1 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 110 := by
  let u : ℝ := inputScale R.input
  have hu : 0 < u := by dsimp [u, inputScale]; positivity
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : Real.logb 2 u * 110 ≤ (n : ℝ) - 4 := by
    dsimp only [u]
    linarith
  have hid : (2 : ℝ) ^ (Real.logb 2 u * (110 : ℕ)) = u ^ 110 := by
    rw [Real.rpow_mul_natCast (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hu]
  have hup : u ^ 110 ≤ (2 : ℝ) ^ n / 16 := by
    calc
      _ = (2 : ℝ) ^ (Real.logb 2 u * (110 : ℕ)) := hid.symm
      _ ≤ (2 : ℝ) ^ ((n : ℝ) - 4) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
      _ = _ := by rw [Real.rpow_sub (by norm_num)]; norm_num
  have hratio : 1 / (2 : ℝ) ^ n ≤ (1 / 10 : ℝ) / u ^ 110 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [show (0 : ℝ) < 2 ^ n by positivity]
  exact (R.samplerError_le_pow hn).trans hratio

theorem bucketHistoryCoupling_failure_guard (hn : 10000 ≤ n)
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000) :
    (R.bucketHistoryCoupling hn).failure ≤
      (1 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 110 :=
  (R.bucketHistoryCoupling_failure hn).trans (R.samplerError_guard hn hscale)

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
