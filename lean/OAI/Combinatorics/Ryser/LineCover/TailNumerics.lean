import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

theorem tendsto_log_pow_mul_rpow_neg_atTop (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun q : ℝ => (Real.log q) ^ k * q ^ (-a)) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun q : ℝ => (Real.log q) ^ k / q ^ a) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (s := a) (k : ℝ) ha).tendsto_div_nhds_zero
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
  simp only [Real.rpow_neg hq, div_eq_mul_inv]

theorem tendsto_rpow_mul_exp_neg_rpow_atTop (r : ℝ) {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun q : ℝ => q ^ r * Real.exp (-c * q ^ a)) atTop (𝓝 0) := by
  refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (r / a) c hc).comp (tendsto_rpow_atTop ha)).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
  dsimp only [Function.comp_apply]
  rw [← Real.rpow_mul hq, mul_div_cancel₀ r ha.ne']

theorem tendsto_polynomial_mul_exp_neg_rpow_atTop (p : Polynomial ℝ) {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun q : ℝ => p.eval q * Real.exp (-c * q ^ a)) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
      simpa only [Polynomial.eval_add, add_mul, add_zero] using hp.add hr
  | monomial k b =>
      simpa only [Polynomial.eval_monomial, Real.rpow_natCast, mul_assoc, mul_zero] using
        (tendsto_rpow_mul_exp_neg_rpow_atTop (k : ℝ) ha hc).const_mul b

theorem tendsto_count_failure_atTop {D ε : ℝ} (hD : 0 < D) (hε : 0 < ε) :
    Tendsto (fun q : ℝ =>
      2 * (1 + q * (q + 1)) * Real.exp (-q ^ (2 * ε) / (16 * D ^ 5)))
      atTop (𝓝 0) := by
  have hc : 0 < (16 * D ^ 5)⁻¹ := by positivity
  have ha : 0 < 2 * ε := by positivity
  have h := tendsto_polynomial_mul_exp_neg_rpow_atTop
    (2 * (1 + Polynomial.X * (Polynomial.X + 1)) : Polynomial ℝ) ha hc
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

def logarithmicSampleSize (A q : ℝ) : ℕ := ⌈A * Real.log q⌉₊

theorem tendsto_logarithmicSampleSize_atTop {A : ℝ} (hA : 0 < A) :
    Tendsto (fun q : ℝ => (logarithmicSampleSize A q : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun q => Nat.le_ceil (A * Real.log q))
  exact Real.tendsto_log_atTop.const_mul_atTop hA

theorem tendsto_sampleSize_pow_mul_rpow_neg_atTop (k : ℕ) {A a : ℝ}
    (hA : 0 < A) (ha : 0 < a) :
    Tendsto (fun q : ℝ => (logarithmicSampleSize A q : ℝ) ^ k * q ^ (-a))
      atTop (𝓝 0) := by
  have hbound : Tendsto
      (fun q : ℝ => (A + 1) ^ k * ((Real.log q) ^ k * q ^ (-a)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_log_pow_mul_rpow_neg_atTop k ha).const_mul
      ((A + 1) ^ k)
  apply squeeze_zero' ?_ ?_ hbound
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hq _)
  · filter_upwards [eventually_ge_atTop (0 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1] with q hq hlog
    have harg : 0 ≤ A * Real.log q := mul_nonneg hA.le (by linarith)
    have hceil : (logarithmicSampleSize A q : ℝ) ≤ A * Real.log q + 1 :=
      (Nat.ceil_lt_add_one harg).le
    have hs : (logarithmicSampleSize A q : ℝ) ≤ (A + 1) * Real.log q := by
      nlinarith
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg (logarithmicSampleSize A q)) hs k
    simpa only [mul_pow, mul_assoc] using
      mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hq (-a))

theorem log_affine_line_count_le {q : ℝ} (hq : 4 ≤ q) :
    Real.log (q * (q + 1)) ≤ (5 / 2 : ℝ) * Real.log q := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q + 1 := by linarith
  have hsmall := Real.log_le_log hq1 (show q + 1 ≤ 2 * q by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hq0.ne'] at hsmall
  have hlarge := Real.log_le_log
    (show 0 < (2 : ℝ) ^ 2 by norm_num) (show (2 : ℝ) ^ 2 ≤ q by nlinarith)
  rw [Real.log_pow] at hlarge
  norm_num only [Nat.cast_ofNat] at hlarge
  rw [Real.log_mul hq0.ne' hq1.ne']
  nlinarith

theorem tuple_failure_le_envelope {q A c0 : ℝ} (t : ℕ) (hq : 4 ≤ q)
    (hA : 0 < A) (ht : A * Real.log q ≤ (t : ℝ)) :
    2 * (q * (q + 1)) ^ (2 * t) * Real.exp (-c0 * (t : ℝ) ^ 2) ≤
      2 * Real.exp (-(c0 - 5 / A) * (t : ℝ) ^ 2) := by
  have hq0 : 0 < q := by linarith
  have hb : 0 < q * (q + 1) := mul_pos hq0 (by linarith)
  have hlog := log_affine_line_count_le hq
  have hcount : (q * (q + 1)) ^ (2 * t) ≤
      Real.exp (5 * (t : ℝ) * Real.log q) := by
    rw [← Real.exp_log (pow_pos hb (2 * t))]
    apply Real.exp_le_exp.mpr
    rw [Real.log_pow]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg t)]
  have hlogDiv : Real.log q ≤ (t : ℝ) / A :=
    (le_div_iff₀ hA).2 (by nlinarith [ht])
  have hexponent : 5 * (t : ℝ) * Real.log q - c0 * (t : ℝ) ^ 2 ≤
      -(c0 - 5 / A) * (t : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hlogDiv
      (show 0 ≤ 5 * (t : ℝ) by positivity)
    simp only [div_eq_mul_inv] at hmul ⊢
    nlinarith
  calc
    2 * (q * (q + 1)) ^ (2 * t) * Real.exp (-c0 * (t : ℝ) ^ 2) ≤
        2 * Real.exp (5 * (t : ℝ) * Real.log q) *
          Real.exp (-c0 * (t : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcount (by norm_num)) (Real.exp_pos _).le
    _ = 2 * Real.exp (5 * (t : ℝ) * Real.log q - c0 * (t : ℝ) ^ 2) := by
      rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg, neg_mul]
    _ ≤ 2 * Real.exp (-(c0 - 5 / A) * (t : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)

theorem tendsto_tuple_failure_atTop {A c0 : ℝ} (hc0 : 0 < c0) (hA : 5 / c0 < A) :
    Tendsto (fun q : ℝ =>
      2 * (q * (q + 1)) ^ (2 * logarithmicSampleSize A q) *
        Real.exp (-c0 * (logarithmicSampleSize A q : ℝ) ^ 2)) atTop (𝓝 0) := by
  have hA0 : 0 < A := lt_trans (div_pos (by norm_num) hc0) hA
  have hfive : 5 < A * c0 := (div_lt_iff₀ hc0).mp hA
  have hcoefficient : 0 < c0 - 5 / A := by
    have hdiv : 5 / A < c0 := (div_lt_iff₀ hA0).2 (by nlinarith)
    linarith
  have hsquare : Tendsto
      (fun q : ℝ => (logarithmicSampleSize A q : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp
      (tendsto_logarithmicSampleSize_atTop hA0)
  have henvelope : Tendsto
      (fun q : ℝ => 2 * Real.exp (-(c0 - 5 / A) *
        (logarithmicSampleSize A q : ℝ) ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_zero, one_mul, mul_zero] using
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        0 (c0 - 5 / A) hcoefficient).comp hsquare).const_mul (2 : ℝ)
  apply squeeze_zero' ?_ ?_ henvelope
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with q hq
    have hq0 : 0 ≤ q := by linarith
    positivity
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with q hq
    exact tuple_failure_le_envelope (logarithmicSampleSize A q) hq hA0
      (Nat.le_ceil (A * Real.log q))

end RyserCoveringCounterexample.LineCover

end

end OAI
