import OAI.Probability.GammaPassage.MGF
import OAI.Probability.GammaPassage.FirstMoment
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Real

/-- Global, signed version of the elementary exponential increment estimate. -/
lemma abs_exp_sub_one_le_abs_mul_exp_abs (x : ℝ) :
    |exp x - 1| ≤ |x| * exp |x| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hx))]
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (exp_pos x).le
    rw [← Real.exp_add] at h
    simp only [neg_add_cancel, Real.exp_zero] at h
    nlinarith
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx', abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hx'))]
    have h₁ := Real.add_one_le_exp x
    have h₂ := mul_le_mul_of_nonneg_left (Real.one_le_exp (neg_nonneg.mpr hx'))
      (neg_nonneg.mpr hx')
    nlinarith

/-- Pointwise domination on the support; it also covers u=0 and a=0. -/
lemma half_exp_increment_square_domination {rate a u : ℝ}
    (hrate : 0 < rate) (ha : |a| ≤ rate / 4) (hu : 0 ≤ u) :
    (exp (a*u/2)-1)^2 ≤ (8 / rate^2 * a^2) * exp ((rate/2)*u) := by
  have hab := abs_exp_sub_one_le_abs_mul_exp_abs (a*u/2)
  have hsq : (exp (a*u/2)-1)^2 ≤
      (a^2*u^2/4) * exp (|a| * u) := by
    have h := mul_self_le_mul_self (abs_nonneg (exp (a*u/2)-1)) hab
    rw [← sq, sq_abs] at h
    have he : (|a * u / 2| * exp |a * u / 2|)^2 =
        (a^2*u^2/4) * exp (|a| * u) := by
      rw [mul_pow, sq_abs]
      have he' : (exp |a * u / 2|)^2 = exp (|a| * u) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        rw [abs_div, abs_mul, abs_of_nonneg hu]
        norm_num
      rw [he']
      ring
    exact h.trans_eq (by simpa only [pow_two] using he)
  have hmono : exp (|a| * u) ≤ exp ((rate/4)*u) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha hu)
  have ht := Real.pow_div_factorial_le_exp ((rate/4)*u) (show 0 ≤ (rate/4)*u by positivity) 2
  norm_num at ht
  have hpoly : u^2 ≤ (32 / rate^2) * exp ((rate/4)*u) := by
    have haux : u^2 ≤ (32 * exp ((rate/4)*u)) / rate^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hrate)).mpr
      nlinarith
    convert haux using 1; ring
  calc
    (exp (a*u/2)-1)^2 ≤ (a^2*u^2/4)*exp ((rate/4)*u) :=
      hsq.trans (mul_le_mul_of_nonneg_left hmono (by positivity))
    _ ≤ (a^2*((32/rate^2)*exp ((rate/4)*u))/4)*exp ((rate/4)*u) := by
      gcongr
    _ = (8/rate^2*a^2)*exp ((rate/2)*u) := by
      have he : exp ((rate/4)*u)*exp ((rate/4)*u) = exp ((rate/2)*u) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (8/rate^2*a^2)*(exp ((rate/4)*u)*exp ((rate/4)*u)) := by ring
        _ = _ := by rw [he]

/-- Integrability follows from a positive Gamma moment at rate/2. -/
theorem gamma_integrable_half_exp_increment_square {shape rate a : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (ha : |a| ≤ rate/4) :
    Integrable (fun u : ℝ => (exp (a*u/2)-1)^2) (gammaMeasure shape rate) := by
  have hi := (gamma_integrable_exp hshape hrate (show rate/2 < rate by linarith)).const_mul
    (8/rate^2*a^2)
  apply hi.mono' (by fun_prop)
  filter_upwards [gamma_ae_pos shape rate] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact half_exp_increment_square_domination hrate ha hu.le

/-- Signed quadratic increment estimate for all positive shape and rate. -/
theorem gamma_integral_half_exp_increment_square_le {shape rate a : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (ha : |a| ≤ rate/4) :
    (∫ u : ℝ, (exp (a*u/2)-1)^2 ∂gammaMeasure shape rate) ≤
      (8*(2 : ℝ)^shape/rate^2)*a^2 := by
  have hi := (gamma_integrable_exp hshape hrate (show rate/2 < rate by linarith)).const_mul
    (8/rate^2*a^2)
  have h := integral_mono_ae (gamma_integrable_half_exp_increment_square hshape hrate ha) hi
    ((gamma_ae_pos shape rate).mono fun u hu => half_exp_increment_square_domination hrate ha hu.le)
  calc
    _ ≤ ∫ u : ℝ, (8/rate^2*a^2)*exp ((rate/2)*u) ∂gammaMeasure shape rate := h
    _ = (8/rate^2*a^2)*(rate/(rate-rate/2))^shape := by
      rw [integral_const_mul, gamma_integral_exp hshape hrate (show rate/2 < rate by linarith)]
    _ = (8*(2 : ℝ)^shape/rate^2)*a^2 := by
      have he : rate/(rate-rate/2) = (2 : ℝ) := by
        apply (div_eq_iff (show rate-rate/2 ≠ 0 by linarith)).mpr
        ring
      rw [he]
      ring
end GammaFPP

end OAI
