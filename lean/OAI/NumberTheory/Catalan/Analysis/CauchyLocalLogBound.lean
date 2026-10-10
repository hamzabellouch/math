import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import OAI.NumberTheory.Catalan.Analysis.CauchyLogJump
import OAI.NumberTheory.Catalan.Estimates.CauchyKernel

namespace OAI

noncomputable section

namespace InternalCatalan

open MeasureTheory Set
open scoped Interval

private theorem imaginary_path_hasDerivAt (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.I * (u : ℂ)) Complex.I t := by
  have hof : HasDerivAt (fun u : ℝ => (u : ℂ)) (1 : ℂ) t := Complex.ofRealCLM.hasDerivAt
  convert! hof.const_mul Complex.I using 1
  simp

theorem cauchyLogLeftPrimitive_hasDerivAt {z : ℂ} (hz : z.re < 0) (t : ℝ) :
    HasDerivAt (fun u : ℝ => -Complex.I * Complex.log (Complex.I * (u : ℂ) - z))
      (1 / (Complex.I * (t : ℂ) - z)) t := by
  have hd : HasDerivAt (fun u : ℝ => Complex.I * (u : ℂ) - z) Complex.I t :=
    (imaginary_path_hasDerivAt t).sub_const z
  have hslit : Complex.I * (t : ℂ) - z ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa [Complex.mul_re, Complex.mul_im] using neg_pos.mpr hz
  have hh := (hd.clog_real hslit).const_mul (-Complex.I)
  convert! hh using 1
  simp only [← mul_div_assoc, neg_mul, Complex.I_mul_I, neg_neg]

theorem cauchyLogRightPrimitive_hasDerivAt {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    HasDerivAt (fun u : ℝ => -Complex.I * Complex.log (z - Complex.I * (u : ℂ)))
      (1 / (Complex.I * (t : ℂ) - z)) t := by
  have hd : HasDerivAt (fun u : ℝ => z - Complex.I * (u : ℂ)) (-Complex.I) t :=
    HasDerivAt.const_sub z (imaginary_path_hasDerivAt t)
  have hslit : z - Complex.I * (t : ℂ) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa [Complex.mul_re, Complex.mul_im] using hz
  have hh := (hd.clog_real hslit).const_mul (-Complex.I)
  convert! hh using 1
  rw [show z - Complex.I * (t : ℂ) = -(Complex.I * (t : ℂ) - z) by ring]
  simp only [div_neg, neg_div, neg_neg, ← mul_div_assoc, neg_mul, Complex.I_mul_I]

theorem intervalIntegrable_cauchyConstantKernel (T : ℝ) {z : ℂ} (hz : z.re ≠ 0) :
    IntervalIntegrable (fun t : ℝ => (1 : ℂ) / (Complex.I * (t : ℂ) - z)) volume (-T) T := by
  have hc : Continuous (fun t : ℝ => (1 : ℂ) / (Complex.I * (t : ℂ) - z)) :=
    continuous_const.div
      ((continuous_const.mul Complex.continuous_ofReal).sub continuous_const)
      (imaginary_sub_ne_zero_of_re_ne_zero hz)
  exact hc.intervalIntegrable _ _

theorem integral_cauchyConstantKernel_eq_left (T : ℝ) {z : ℂ} (hz : z.re < 0) :
    (∫ t in -T..T, (1 : ℂ) / (Complex.I * (t : ℂ) - z)) = cauchyLogLeft T z := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (-T) T) => cauchyLogLeftPrimitive_hasDerivAt hz t)
    (intervalIntegrable_cauchyConstantKernel T hz.ne)
  rw [hi]
  unfold cauchyLogLeft
  simp only [Complex.ofReal_neg, mul_neg, neg_mul]
  ring

theorem integral_cauchyConstantKernel_eq_right (T : ℝ) {z : ℂ} (hz : 0 < z.re) :
    (∫ t in -T..T, (1 : ℂ) / (Complex.I * (t : ℂ) - z)) = cauchyLogRight T z := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (-T) T) => cauchyLogRightPrimitive_hasDerivAt hz t)
    (intervalIntegrable_cauchyConstantKernel T hz.ne')
  rw [hi]
  unfold cauchyLogRight
  simp only [Complex.ofReal_neg, mul_neg, sub_neg_eq_add]
  ring

open MeasureTheory Set
open scoped Interval

theorem log_two_mul_nat_le (n : ℕ) (hn : 0 < n) :
    Real.log (2 * (n : ℝ)) ≤ n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [Real.log_mul (by norm_num) hnR.ne']
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hnlog := Real.log_le_sub_one_of_pos hnR
  linarith

theorem complex_log_norm_le_nat_add_pi (n : ℕ) (hn : 0 < n) {w : ℂ}
    (hlo : 1 / (2 * (n : ℝ)) ≤ ‖w‖) (hhi : ‖w‖ ≤ 1) :
    ‖Complex.log w‖ ≤ (n : ℝ) + Real.pi := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hloglo : -Real.log (2 * (n : ℝ)) ≤ Real.log ‖w‖ := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < 1 / (2 * (n : ℝ))) hlo
    simpa only [one_div, Real.log_inv] using hh
  have hloghi : Real.log ‖w‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) hhi
  have habs : |Real.log ‖w‖| ≤ (n : ℝ) := by
    rw [abs_of_nonpos hloghi]
    linarith [log_two_mul_nat_le n hn]
  calc
    _ ≤ |(Complex.log w).re| + |(Complex.log w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (n : ℝ) + Real.pi := by
      rw [Complex.log_re, Complex.log_im]
      exact add_le_add habs (Complex.abs_arg_le_pi w)

theorem intervalIntegrable_cauchyConstantKernel_interval (a b : ℝ) {z : ℂ} (hz : z.re ≠ 0) :
    IntervalIntegrable (fun t : ℝ => (1 : ℂ) / (Complex.I * (t : ℂ) - z)) volume a b := by
  have hc : Continuous (fun t : ℝ => (1 : ℂ) / (Complex.I * (t : ℂ) - z)) :=
    continuous_const.div
      ((continuous_const.mul Complex.continuous_ofReal).sub continuous_const)
      (imaginary_sub_ne_zero_of_re_ne_zero hz)
  exact hc.intervalIntegrable _ _

theorem cauchyConstantKernel_interval_norm_le_three_mul (n : ℕ) (hn : 48 ≤ n)
    (a b : ℝ) {z : ℂ} (hz : z.re ≠ 0)
    (hal : 1 / (2 * (n : ℝ)) ≤ ‖Complex.I * (a : ℂ) - z‖)
    (hau : ‖Complex.I * (a : ℂ) - z‖ ≤ 1)
    (hbl : 1 / (2 * (n : ℝ)) ≤ ‖Complex.I * (b : ℂ) - z‖)
    (hbu : ‖Complex.I * (b : ℂ) - z‖ ≤ 1) :
    ‖∫ t in a..b, (1 : ℂ) / (Complex.I * (t : ℂ) - z)‖ ≤ 3 * (n : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have hfinal : 2 * ((n : ℝ) + Real.pi) ≤ 3 * (n : ℝ) := by linarith [Real.pi_lt_four]
  rcases lt_or_gt_of_ne hz with hz | hz
  · have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t (_ : t ∈ uIcc a b) => cauchyLogLeftPrimitive_hasDerivAt hz t)
      (intervalIntegrable_cauchyConstantKernel_interval a b hz.ne)
    rw [hi]
    calc
      _ ≤ ‖-Complex.I * Complex.log (Complex.I * (b : ℂ) - z)‖ +
          ‖-Complex.I * Complex.log (Complex.I * (a : ℂ) - z)‖ := norm_sub_le _ _
      _ ≤ 2 * ((n : ℝ) + Real.pi) := by
        simp only [norm_mul, norm_neg, Complex.norm_I, one_mul]
        linarith [complex_log_norm_le_nat_add_pi n hn0 hal hau,
          complex_log_norm_le_nat_add_pi n hn0 hbl hbu]
      _ ≤ 3 * (n : ℝ) := hfinal
  · have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t (_ : t ∈ uIcc a b) => cauchyLogRightPrimitive_hasDerivAt hz t)
      (intervalIntegrable_cauchyConstantKernel_interval a b hz.ne')
    have ha1 : 1 / (2 * (n : ℝ)) ≤ ‖z - Complex.I * (a : ℂ)‖ := by rwa [norm_sub_rev]
    have ha2 : ‖z - Complex.I * (a : ℂ)‖ ≤ 1 := by rwa [norm_sub_rev]
    have hb1 : 1 / (2 * (n : ℝ)) ≤ ‖z - Complex.I * (b : ℂ)‖ := by rwa [norm_sub_rev]
    have hb2 : ‖z - Complex.I * (b : ℂ)‖ ≤ 1 := by rwa [norm_sub_rev]
    rw [hi]
    calc
      _ ≤ ‖-Complex.I * Complex.log (z - Complex.I * (b : ℂ))‖ +
          ‖-Complex.I * Complex.log (z - Complex.I * (a : ℂ))‖ := norm_sub_le _ _
      _ ≤ 2 * ((n : ℝ) + Real.pi) := by
        simp only [norm_mul, norm_neg, Complex.norm_I, one_mul]
        linarith [complex_log_norm_le_nat_add_pi n hn0 ha1 ha2,
          complex_log_norm_le_nat_add_pi n hn0 hb1 hb2]
      _ ≤ 3 * (n : ℝ) := hfinal

end InternalCatalan

end

end OAI
