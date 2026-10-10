import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BoxNonneg

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinarySharpWindow
open MeasureTheory Finset

lemma sharp_weight_term_error (a : ℂ) (u H x : ℝ) :
    ‖(Real.exp (-x):ℂ)*(a*(Real.exp u:ℂ)*(box H (x-u):ℂ))-
      a*(box H (x-u):ℂ)‖ ≤ H*‖a‖*box H (x-u) := by
  by_cases hx : x-u∈Set.Ioc 0 H
  · have he : Real.exp (u-x) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      linarith [hx.1]
    have hlo := Real.add_one_le_exp (u-x)
    have hdiff : |Real.exp (u-x)-1| ≤ H := by
      rw [abs_of_nonpos (by linarith)]
      linarith [hx.2]
    have heq : (Real.exp (-x):ℂ)*(a*(Real.exp u:ℂ))-a=
        a*((Real.exp (u-x)-1:ℝ):ℂ) := by
      rw [Complex.ofReal_sub,Real.exp_sub]
      rw [Real.exp_neg,Complex.ofReal_div,Complex.ofReal_inv,Complex.ofReal_one]
      ring
    simp only [box,Set.indicator_of_mem hx,Complex.ofReal_one,mul_one,heq,norm_mul,
      Complex.norm_real,Real.norm_eq_abs]
    nlinarith only [mul_le_mul_of_nonneg_left hdiff (norm_nonneg a)]
  · simp only [box,Set.indicator_of_notMem hx,Complex.ofReal_zero,mul_zero,sub_zero,norm_zero,le_refl]

lemma sharp_weight_pointwise {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    (H x : ℝ) :
    Real.exp (-x)*‖sharpWindow s (fun n=>a n*(Real.exp (u n):ℂ)) u H x‖ ≤
      ‖sharpWindow s a u H x‖+H*(∑n∈s,‖a n‖*box H (x-u n)) := by
  let S := sharpWindow s (fun n=>a n*(Real.exp (u n):ℂ)) u H x
  let V := sharpWindow s a u H x
  have he : Real.exp (-x)*‖S‖=‖(Real.exp (-x):ℂ)*S‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  rw [he]
  have hh : ‖(Real.exp (-x):ℂ)*S-V‖ ≤ H*(∑n∈s,‖a n‖*box H (x-u n)) := by
    dsimp [S,V,sharpWindow]
    rw [mul_sum,←sum_sub_distrib,mul_sum]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro n hn
    exact (sharp_weight_term_error (a n) (u n) H x).trans_eq (by ring)
  have ht := norm_le_insert' ((Real.exp (-x):ℂ)*S) V
  linarith only [hh,ht]

theorem sharp_weight_removal {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {H : ℝ} (hH : 0 ≤ H) :
    Integrable (fun x : ℝ=>Real.exp (-x)*
      ‖sharpWindow s (fun n=>a n*(Real.exp (u n):ℂ)) u H x‖) ∧
    (∫x : ℝ,Real.exp (-x)*‖sharpWindow s (fun n=>a n*(Real.exp (u n):ℂ)) u H x‖) ≤
      (∫x : ℝ,‖sharpWindow s a u H x‖)+H^2*(∑n∈s,‖a n‖) := by
  have hterms (n : ι) : Integrable (fun x : ℝ=>‖a n‖*box H (x-u n)) :=
    ((box_integrable H).comp_sub_right (u n)).const_mul _
  have hdom := (sharpWindow_integrable s a u H).norm.add
    ((integrable_finsetSum s (fun n hn=>hterms n)).const_mul H)
  have hsm := ((sharpWindow_integrable s (fun n=>a n*(Real.exp (u n):ℂ)) u H).norm.aestronglyMeasurable)
  have hmeas : AEStronglyMeasurable (fun x : ℝ=>Real.exp (-x)*
      ‖sharpWindow s (fun n=>a n*(Real.exp (u n):ℂ)) u H x‖) :=
    (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable.mul hsm
  have hi : Integrable (fun x : ℝ=>Real.exp (-x)*
      ‖sharpWindow s (fun n=>a n*(Real.exp (u n):ℂ)) u H x‖) := by
    apply Integrable.mono' hdom hmeas
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
    exact sharp_weight_pointwise s a u H x
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫x : ℝ,‖sharpWindow s a u H x‖+H*(∑n∈s,‖a n‖*box H (x-u n)) :=
      integral_mono hi hdom (sharp_weight_pointwise s a u H)
    _ = _ := by
      rw [integral_add (sharpWindow_integrable s a u H).norm
        ((integrable_finsetSum s (fun n hn=>hterms n)).const_mul H),MeasureTheory.integral_const_mul,
        integral_finsetSum s (fun n hn=>hterms n)]
      have he (n : ι) : (∫x : ℝ,‖a n‖*box H (x-u n))=‖a n‖*H := by
        rw [MeasureTheory.integral_const_mul,integral_sub_right_eq_self,box_integral hH]
      simp_rw [he]
      rw [←sum_mul]
      ring

end OrdinarySharpWindow

end

end OAI
