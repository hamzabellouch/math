import OAI.Probability.InvariantIsing.Gaussian.MPTrigonometricDenominator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! An elementary antiderivative for the denominator in the MP density integral. -/
noncomputable section
open Real Set
namespace InvariantIsing

def mpAnglePrimitive (a b x : ℝ) : ℝ :=
  arccos ((a*cos x+b)/(a+b*cos x))/sqrt (a^2-b^2)

lemma mp_cos_fraction_sqrt {a b : ℝ} (hab : |b| < a) {x : ℝ} (hx : x ∈ Ioo 0 Real.pi) :
    sqrt (1-((a*cos x+b)/(a+b*cos x))^2) =
      sqrt (a^2-b^2)*sin x/(a+b*cos x) := by
  rw [mp_cos_fraction_identity hab x,
    sqrt_div (mul_nonneg (mp_discriminant_pos hab).le (sq_nonneg _)),
    sqrt_mul (mp_discriminant_pos hab).le,
    sqrt_sq (sin_pos_of_pos_of_lt_pi hx.1 hx.2).le,
    sqrt_sq (mp_cos_denominator_pos hab x).le]

lemma mpAnglePrimitive_hasDerivAt {a b : ℝ} (hab : |b| < a) {x : ℝ} (hx : x ∈ Ioo 0 Real.pi) :
    HasDerivAt (mpAnglePrimitive a b) (1/(a+b*cos x)) x := by
  have hm := mp_cos_fraction_mem_Ioo hab hx
  have hc := (hasDerivAt_arccos (ne_of_gt hm.1) (ne_of_lt hm.2)).comp x
    (mp_cos_fraction_hasDerivAt hab x)
  have hs := sqrt_pos.mpr (mp_discriminant_pos hab)
  have hd := mp_cos_denominator_pos hab x
  have hsin := sin_pos_of_pos_of_lt_pi hx.1 hx.2
  unfold mpAnglePrimitive
  have hc' := hc.div_const (sqrt (a^2-b^2))
  simp only [Function.comp_def] at hc'
  convert hc' using 1
  rw [mp_cos_fraction_sqrt hab hx]
  have hsq := sq_sqrt (mp_discriminant_pos hab).le
  field_simp [hs.ne',hd.ne',hsin.ne']
  nlinarith

lemma continuous_mpAnglePrimitive {a b : ℝ} (hab : |b| < a) :
    Continuous (mpAnglePrimitive a b) := by
  unfold mpAnglePrimitive
  apply Continuous.div_const
  apply continuous_arccos.comp
  exact ((continuous_const.mul continuous_cos).add continuous_const).div
    (continuous_const.add (continuous_const.mul continuous_cos))
    (fun x => (mp_cos_denominator_pos hab x).ne')

theorem mp_integral_cos_denominator {a b : ℝ} (hab : |b| < a) :
    (∫ x in (0 : ℝ)..Real.pi, 1/(a+b*cos x)) = Real.pi/sqrt (a^2-b^2) := by
  have hi : IntervalIntegrable (fun x : ℝ => 1/(a+b*cos x)) MeasureTheory.volume 0 Real.pi :=
    (continuous_const.div (continuous_const.add (continuous_const.mul continuous_cos))
      (fun x => (mp_cos_denominator_pos hab x).ne')).intervalIntegrable 0 Real.pi
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le pi_pos.le
    (continuous_mpAnglePrimitive hab).continuousOn (fun x hx => mpAnglePrimitive_hasDerivAt hab hx) hi
  have hp : a+b ≠ 0 := by simpa using (mp_cos_denominator_pos hab 0).ne'
  have hn : a-b ≠ 0 := by simpa only [cos_pi,mul_neg_one,sub_eq_add_neg] using (mp_cos_denominator_pos hab Real.pi).ne'
  have he : (a*(-1)+b)/(a+b*(-1)) = -1 := by
    apply (div_eq_iff (show a+b*(-1) ≠ 0 by simpa only [mul_neg_one,sub_eq_add_neg] using hn)).mpr
    ring
  simpa only [mpAnglePrimitive,cos_zero,cos_pi,mul_one,he,div_self hp,
    arccos_one,arccos_neg_one,zero_div,sub_zero] using h

end InvariantIsing

end

end OAI
