import Mathlib
import OAI.Probability.SKValue.Evolution.BoundedSmooth

namespace OAI

section

open MeasureTheory Set
open scoped Topology
namespace SKValue

lemma inv_sqrt_eq_rpow {x : ℝ} (hx : 0 ≤ x) : (Real.sqrt x)⁻¹=x^(-(1/2 : ℝ)) := by
  rw [Real.rpow_neg hx,Real.sqrt_eq_rpow]

lemma intervalIntegrable_inv_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun s : ℝ ↦ (Real.sqrt s)⁻¹) volume a b := by
  apply (intervalIntegral.intervalIntegrable_rpow' (a := a) (b := b) (r := -(1/2 : ℝ)) (by norm_num)).congr
  intro s hs
  exact (inv_sqrt_eq_rpow ((le_min ha hb).trans hs.1.le)).symm

lemma integral_inv_sqrt {d : ℝ} (hd : 0 ≤ d) :
    (∫ s in (0 : ℝ)..d, (Real.sqrt s)⁻¹) = 2*Real.sqrt d := by
  calc
    _ = ∫ s in (0 : ℝ)..d, s^(-(1/2 : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hd] at hs
      exact inv_sqrt_eq_rpow hs.1
    _ = _ := by
      rw [integral_rpow (Or.inl (by norm_num))]
      norm_num [Real.sqrt_eq_rpow]
      ring

lemma intervalIntegrable_inv_sqrt_sub {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun s : ℝ ↦ (Real.sqrt (s-a))⁻¹) volume a b := by
  have h := (intervalIntegrable_inv_sqrt (a := 0) (b := b-a) le_rfl (sub_nonneg.mpr hab)).comp_sub_right a
  simpa only [zero_add,sub_add_cancel] using h

lemma intervalIntegrable_inv_sqrt_sub_left {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun s : ℝ ↦ (Real.sqrt (b-s))⁻¹) volume a b := by
  have h := (intervalIntegrable_inv_sqrt (a := 0) (b := b-a) le_rfl (sub_nonneg.mpr hab)).comp_sub_left b
  simpa only [sub_sub_cancel,sub_zero] using h.symm

lemma integral_inv_sqrt_sub {a b : ℝ} (hab : a ≤ b) :
    (∫ s in a..b, (Real.sqrt (s-a))⁻¹)=2*Real.sqrt (b-a) := by
  rw [intervalIntegral.integral_comp_sub_right (fun s : ℝ ↦ (Real.sqrt s)⁻¹),sub_self,integral_inv_sqrt (sub_nonneg.mpr hab)]

lemma integral_inv_sqrt_sub_left {a b : ℝ} (hab : a ≤ b) :
    (∫ s in a..b, (Real.sqrt (b-s))⁻¹)=2*Real.sqrt (b-a) := by
  rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ ↦ (Real.sqrt s)⁻¹),sub_self,integral_inv_sqrt (sub_nonneg.mpr hab)]

noncomputable def sqrtKernel (a b s : ℝ) : ℝ := (Real.sqrt (s-a))⁻¹*(Real.sqrt (b-s))⁻¹
noncomputable def sqrtMajorant (a b s : ℝ) : ℝ :=
  (2/Real.sqrt (b-a))*((Real.sqrt (s-a))⁻¹+(Real.sqrt (b-s))⁻¹)

lemma sqrtKernel_nonneg (a b s : ℝ) : 0 ≤ sqrtKernel a b s := by unfold sqrtKernel; positivity

lemma sqrtKernel_le_majorant {a b s : ℝ} (hab : a<b) (hs : s∈Icc a b) :
    sqrtKernel a b s ≤ sqrtMajorant a b s := by
  have hd := Real.sqrt_pos.mpr (sub_pos.mpr hab)
  have hD := Real.sq_sqrt (sub_nonneg.mpr hab.le)
  have hx := Real.sq_sqrt (sub_nonneg.mpr hs.1)
  have hy := Real.sq_sqrt (sub_nonneg.mpr hs.2)
  have hsx := Real.sqrt_nonneg (s-a)
  have hsy := Real.sqrt_nonneg (b-s)
  unfold sqrtKernel sqrtMajorant
  by_cases hsa : s=a
  · subst s
    simp only [sub_self,Real.sqrt_zero,inv_zero,zero_mul,zero_add]
    positivity
  by_cases hsb : s=b
  · subst s
    simp only [sub_self,Real.sqrt_zero,inv_zero,mul_zero,add_zero]
    positivity
  have hxpos := Real.sqrt_pos.mpr (sub_pos.mpr (lt_of_le_of_ne hs.1 (Ne.symm hsa)))
  have hypos := Real.sqrt_pos.mpr (sub_pos.mpr (lt_of_le_of_ne hs.2 hsb))
  have hc : 0 ≤ 2/Real.sqrt (b-a) := by positivity
  by_cases hm : (b-a)/2 ≤ s-a
  · have hsqrt : Real.sqrt (b-a) ≤ 2*Real.sqrt (s-a) := by nlinarith
    have hi : (Real.sqrt (s-a))⁻¹ ≤ 2/Real.sqrt (b-a) := by
      rw [inv_eq_one_div,div_le_div_iff₀ hxpos hd]
      nlinarith
    calc
      _  ≤  (2/Real.sqrt (b-a))*(Real.sqrt (b-s))⁻¹ := mul_le_mul_of_nonneg_right hi (by positivity)
      _  ≤  _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hc
  · have hsqrt : Real.sqrt (b-a) ≤ 2*Real.sqrt (b-s) := by nlinarith
    have hi : (Real.sqrt (b-s))⁻¹ ≤ 2/Real.sqrt (b-a) := by
      rw [inv_eq_one_div,div_le_div_iff₀ hypos hd]
      nlinarith
    calc
      _  ≤  (Real.sqrt (s-a))⁻¹*(2/Real.sqrt (b-a)) := mul_le_mul_of_nonneg_left hi (by positivity)
      _  ≤  _ := by nlinarith [mul_nonneg hc (inv_nonneg.mpr hsy)]

lemma sqrtMajorant_integrable {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (sqrtMajorant a b) volume a b :=
  ((intervalIntegrable_inv_sqrt_sub hab).add (intervalIntegrable_inv_sqrt_sub_left hab)).const_mul _

lemma sqrtKernel_integrable {a b : ℝ} (hab : a<b) :
    IntervalIntegrable (sqrtKernel a b) volume a b := by
  apply (sqrtMajorant_integrable hab.le).mono_fun'
  · exact (((measurable_id.sub_const a).sqrt.inv).mul
      ((measurable_const.sub measurable_id).sqrt.inv)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le hab.le] at hs
    rw [Real.norm_eq_abs,abs_of_nonneg (sqrtKernel_nonneg a b s)]
    exact sqrtKernel_le_majorant hab ⟨hs.1.le,hs.2⟩

lemma sqrtKernel_integral_le_eight {a b : ℝ} (hab : a<b) :
    (∫ s in a..b, sqrtKernel a b s) ≤ 8 := by
  have hd := Real.sqrt_ne_zero'.mpr (sub_pos.mpr hab)
  calc
    _  ≤  ∫ s in a..b, sqrtMajorant a b s :=
      intervalIntegral.integral_mono_on hab.le (sqrtKernel_integrable hab)
        (sqrtMajorant_integrable hab.le) (fun s hs ↦ sqrtKernel_le_majorant hab hs)
    _ = (2/Real.sqrt (b-a))*(2*Real.sqrt (b-a)+2*Real.sqrt (b-a)) := by
      unfold sqrtMajorant
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
        (intervalIntegrable_inv_sqrt_sub hab.le) (intervalIntegrable_inv_sqrt_sub_left hab.le),
        integral_inv_sqrt_sub hab.le,integral_inv_sqrt_sub_left hab.le]
    _ = 8 := by field_simp; ring

end SKValue

end

end OAI
