import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticErrorRates
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternCostRate

namespace OAI

/-! # The actual internal arithmetic error at the source's prime scales -/

namespace Ostmann
open Filter

noncomputable def movingInternalArithmeticError (n c d : ℕ) (F U α β V : ℝ) : ℝ :=
  ((2 * (2 ^ n - 1 : ℕ)) * c * Real.exp (-V)) +
    2 * ((c * (2 + 2 * (2 ^ n - 1)) : ℕ) : ℝ) *
      ((2 * ((n + 1) * d) : ℕ) * α +
        (Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) / V) * β)

/-- The logarithm of the polynomial height, before the prime-divisor count.
Only the sampled-coordinate lower cutoff will divide this expression. -/
theorem moving_internal_log_height (n d : ℕ) (F U C D L : ℝ)
    (hF : 1 ≤ F) (hU : 1 ≤ U) (hC : 0 ≤ C) (hD : 0 ≤ D) (hL : 1 ≤ L)
    (hfreq : Real.log F ≤ C * L) (hdegree : (d : ℝ) ≤ D * L)
    (hvalue : Real.log U ≤ Real.exp ((12 / 1000 : ℝ) * L)) :
    Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) ≤
      (1 + 2 * ((n : ℝ) + 1) * (1 + C + D)) * L *
        Real.exp ((12 / 1000 : ℝ) * L) := by
  have hF0 : 0 < F := lt_of_lt_of_le (by norm_num) hF
  have hU0 : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hexp : 1 ≤ Real.exp ((12 / 1000 : ℝ) * L) :=
    Real.one_le_exp_iff.mpr (by linarith)
  have heq : Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) =
      Real.log 2 + 2 * ((n : ℝ) + 1) *
        (Real.log 2 + Real.log F + (d : ℝ) * Real.log U) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity), Real.log_pow,
      Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity),
      Real.log_mul hF0.ne' (pow_ne_zero _ hU0.ne'), Real.log_pow]
    push_cast
    ring
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hd : (d : ℝ) * Real.log U ≤ D * L * Real.exp ((12 / 1000 : ℝ) * L) :=
    mul_le_mul hdegree hvalue (Real.log_nonneg hU) (by positivity)
  have hCL : C * L ≤ C * L * Real.exp ((12 / 1000 : ℝ) * L) :=
    le_mul_of_one_le_right (by positivity) hexp
  have hunit : 1 ≤ L * Real.exp ((12 / 1000 : ℝ) * L) :=
    one_le_mul_of_one_le_of_one_le hL hexp
  have hinn : Real.log 2 + Real.log F + (d : ℝ) * Real.log U ≤
      (1 + C + D) * L * Real.exp ((12 / 1000 : ℝ) * L) := by
    nlinarith
  rw [heq]
  have hm := mul_le_mul_of_nonneg_left hinn
    (show 0 ≤ 2 * ((n : ℝ) + 1) by positivity)
  nlinarith

/-- The source's three internal errors have a common exponential saving.
The prime-divisor term is evaluated with the internal-prime cutoff. -/
theorem moving_internal_error_small (n c : ℕ) (C D E : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    ∀ᶠ L : ℝ in atTop, ∀ (d : ℕ) (F U α β : ℝ),
      1 ≤ F → 1 ≤ U → 0 ≤ α →
      α ≤ Real.exp (E * L - Real.exp ((39 / 10000 : ℝ) * L)) → 0 ≤ β →
      Real.log F ≤ C * L → (d : ℝ) ≤ D * L →
      Real.log U ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      β ≤ Real.exp (E * L - Real.exp ((1 / 100 : ℝ) * L)) →
      movingInternalArithmeticError n c d F U α β (Real.exp ((1 / 100 : ℝ) * L)) ≤
      Real.exp (-((1 / 2 : ℝ) * Real.exp ((39 / 10000 : ℝ) * L))) := by
  let K : ℝ := 1 + 2 * ((n : ℝ) + 1) * (1 + C + D)
  let a : ℝ := (2 * (2 ^ n - 1 : ℕ)) * c
  let b : ℝ := 2 * (c * (2 + 2 * (2 ^ n - 1)) : ℕ)
  let H : ℝ := a + b * (2 * ((n : ℝ) + 1) * D + K)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hrate := arithmetic_exponent_absorption 0 (39 / 10000) 0
    (H + E + 12 / 1000) (1 / 2) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [hrate, eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro d F U α β hF hU hα0 hα hβ hfreq hdegree hvalue hβbound
  have hheight := moving_internal_log_height n d F U C D L hF hU hC hD hL hfreq hdegree hvalue
  have hV : 1 ≤ Real.exp ((1 / 100 : ℝ) * L) :=
    Real.one_le_exp_iff.mpr (by linarith)
  have hheight0 : 0 ≤ Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) := by
    apply Real.log_nonneg
    have hbase : 1 ≤ 2 * (F * U ^ d) := by
      have := one_le_mul_of_one_le_of_one_le hF (one_le_pow₀ hU (n := d))
      linarith
    have := one_le_pow₀ (one_le_pow₀ hbase (n := n + 1)) (n := 2)
    linarith
  have hquot : Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) /
      Real.exp ((1 / 100 : ℝ) * L) ≤ K * L * Real.exp ((12 / 1000 : ℝ) * L) :=
    (div_le_self hheight0 hV).trans hheight
  have hdeg : ((2 * ((n + 1) * d) : ℕ) : ℝ) ≤ 2 * ((n : ℝ) + 1) * D * L := by
    push_cast
    have hh := mul_le_mul_of_nonneg_left hdegree (show 0 ≤ 2 * ((n : ℝ) + 1) by positivity)
    nlinarith
  have hsave : Real.exp ((39 / 10000 : ℝ) * L) ≤ Real.exp ((1 / 100 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by linarith)
  have hβcommon : β ≤ Real.exp (E * L - Real.exp ((39 / 10000 : ℝ) * L)) :=
    hβbound.trans (Real.exp_le_exp.mpr (by linarith))
  have hexp : 1 ≤ Real.exp ((12 / 1000 : ℝ) * L) :=
    Real.one_le_exp_iff.mpr (by linarith)
  have hunit : 1 ≤ L * Real.exp ((12 / 1000 : ℝ) * L) :=
    one_le_mul_of_one_le_of_one_le hL hexp
  have he0 : 0 ≤ E * L := mul_nonneg hE (by linarith)
  have he : Real.exp (-Real.exp ((1 / 100 : ℝ) * L)) ≤
      Real.exp (E * L - Real.exp ((39 / 10000 : ℝ) * L)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hterms :
      a * Real.exp (-Real.exp ((1 / 100 : ℝ) * L)) +
        b * (((2 * ((n + 1) * d) : ℕ) : ℝ) * α +
          Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) /
            Real.exp ((1 / 100 : ℝ) * L) * β) ≤
      H * L * Real.exp ((12 / 1000 : ℝ) * L) *
        Real.exp (E * L - Real.exp ((39 / 10000 : ℝ) * L)) := by
    have hdeg' : 2 * ((n : ℝ) + 1) * D * L ≤
        2 * ((n : ℝ) + 1) * D * L * Real.exp ((12 / 1000 : ℝ) * L) :=
      le_mul_of_one_le_right (by positivity) hexp
    have hαterm := mul_le_mul hdeg hα hα0 (by positivity)
    have hβterm := mul_le_mul hquot hβcommon hβ (by positivity)
    have hsum := add_le_add hαterm hβterm
    have hsum' :
        ((2 * ((n + 1) * d) : ℕ) : ℝ) * α +
            Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) /
              Real.exp ((1 / 100 : ℝ) * L) * β ≤
        (2 * ((n : ℝ) + 1) * D * L + K * L * Real.exp ((12 / 1000 : ℝ) * L)) *
          Real.exp (E * L - Real.exp ((39 / 10000 : ℝ) * L)) :=
      hsum.trans_eq (by ring)
    have hbm := mul_le_mul_of_nonneg_left
      (hsum'.trans (mul_le_mul_of_nonneg_right (add_le_add hdeg' le_rfl) (Real.exp_nonneg _))) hb
    have ham := mul_le_mul_of_nonneg_left he ha
    have ha' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hunit ha)
      (Real.exp_nonneg (E * L - Real.exp ((39 / 10000 : ℝ) * L)))
    simp only [mul_one] at ha'
    exact (add_le_add (ham.trans ha') hbm).trans_eq (by dsimp only [H]; ring)
  change a * _ + b * _ ≤ _
  apply hterms.trans
  have hpref : H * L ≤ Real.exp (H * L) := by
    linarith [Real.add_one_le_exp (H * L)]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpref (Real.exp_nonneg ((12 / 1000 : ℝ) * L)))
    (Real.exp_nonneg (E * L - Real.exp ((39 / 10000 : ℝ) * L)))
  apply hh.trans
  simp only [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [pow_one, zero_mul, Real.exp_zero, mul_one] at hrate
  have : (H + E + 12 / 1000) * L ≤ (1 / 2 : ℝ) * Real.exp ((39 / 10000 : ℝ) * L) := by
    have hc : 0 ≤ (H + E + 12 / 1000) * L := by positivity
    nlinarith
  linarith

/-- Summing equality patterns and paying the true pointwise kernel/spectator
cost still leaves the stated internal-prime error. -/
theorem moving_internal_error_with_cost (n c : ℕ) (C D E Cprior B : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (hCprior : 1 ≤ Cprior) (_hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop, ∀ (d : ℕ) (F U α β : ℝ),
      1 ≤ F → 1 ≤ U → 0 ≤ α →
      α ≤ Real.exp (E * L - Real.exp ((39 / 10000 : ℝ) * L)) → 0 ≤ β →
      Real.log F ≤ C * L → (d : ℝ) ≤ D * L →
      Real.log U ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      β ≤ Real.exp (E * L - Real.exp ((1 / 100 : ℝ) * L)) →
      ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
        Real.exp (B * L ^ 2 + B * L * Real.exp ((1 / 1000 : ℝ) * L)) *
        movingInternalArithmeticError n c d F U α β (Real.exp ((1 / 100 : ℝ) * L)) ≤
          Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  let J : ℝ := ((4 * n * 2 ^ n) ^ 2 + 4 * n * 2 ^ n : ℕ)
  let B' := B + J * Cprior
  filter_upwards [moving_internal_error_small n c C D E hC hD hE,
    arithmetic_error_absorption (1 / 1000) (39 / 10000) (2 / 1000) B' (1 / 2) 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hsmall hcost hL
  intro d F U α β hF hU hα0 hα hβ hfreq hdegree hvalue hβbound
  have hJ : 0 ≤ J := by positivity
  have hJL : J * Cprior * L ≤ J * Cprior * L ^ 2 := by
    have hC0 : 0 ≤ Cprior := by linarith
    exact mul_le_mul_of_nonneg_left (by nlinarith : L ≤ L ^ 2) (mul_nonneg hJ hC0)
  have hrest : B * L * Real.exp ((1 / 1000 : ℝ) * L) ≤
      B' * L * Real.exp ((1 / 1000 : ℝ) * L) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    dsimp only [B']
    nlinarith [mul_nonneg hJ (show 0 ≤ Cprior by linarith)]
  have hbudget :
      ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
        Real.exp (B * L ^ 2 + B * L * Real.exp ((1 / 1000 : ℝ) * L)) ≤
      Real.exp (B' * L ^ 2 + B' * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
    apply (mul_le_mul_of_nonneg_right
      (movingPattern_total_cost_le_exp n Cprior L hCprior hL) (Real.exp_nonneg _)).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp only [B']
    nlinarith
  have hs := hsmall d F U α β hF hU hα0 hα hβ hfreq hdegree hvalue hβbound
  exact ((mul_le_mul_of_nonneg_left hs (by positivity)).trans
    (mul_le_mul_of_nonneg_right hbudget (Real.exp_nonneg _))).trans
      (by simpa only [neg_mul] using hcost)

end Ostmann

end OAI
