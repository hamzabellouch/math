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

lemma sharpWindow_zero_high {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {U H x : ℝ} (hu : ∀n∈s,u n ≤ U) (hx : U+H < x) : sharpWindow s a u H x=0 := by
  apply sum_eq_zero
  intro n hn
  have hh : x-u n∉Set.Ioc 0 H := by
    intro hh
    linarith [hh.2,hu n hn]
  simp [box,Set.indicator_of_notMem hh]

lemma exp_sharp_bound {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {U H : ℝ} (hu : ∀n∈s,u n ≤ U) (x : ℝ) :
    Real.exp x*‖sharpWindow s a u H x‖ ≤
      Real.exp (2*(U+H))*(Real.exp (-x)*‖sharpWindow s a u H x‖) := by
  by_cases hx : x ≤ U+H
  · have hh : Real.exp x ≤ Real.exp (2*(U+H))*Real.exp (-x) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith only [hx]
    nlinarith only [mul_le_mul_of_nonneg_right hh (norm_nonneg (sharpWindow s a u H x))]
  · rw [sharpWindow_zero_high s a u hu (lt_of_not_ge hx)]
    simp

lemma integral_exp_substitution (V : ℝ→ℝ) :
    (∫y in Set.Ioi (0:ℝ),V (Real.log y))=∫x : ℝ,Real.exp x*V x := by
  have hh := integral_image_eq_integral_abs_deriv_smul (s:=Set.univ)
    MeasurableSet.univ (fun x _=>(Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun y : ℝ=>V (Real.log y))
  simpa only [Set.image_univ,Real.range_exp,Real.log_exp,abs_of_pos (Real.exp_pos _),
    Measure.restrict_univ,smul_eq_mul] using hh

lemma sharp_physical_integral_bound {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {U H : ℝ} (hu : ∀n∈s,u n ≤ U)
    (hi : Integrable (fun x : ℝ=>Real.exp (-x)*‖sharpWindow s a u H x‖)) :
    (∫y in Set.Ioi (0:ℝ),‖sharpWindow s a u H (Real.log y)‖) ≤
      Real.exp (2*(U+H))*(∫x : ℝ,Real.exp (-x)*‖sharpWindow s a u H x‖) := by
  rw [integral_exp_substitution (fun x=>‖sharpWindow s a u H x‖)]
  have hsm := (sharpWindow_integrable s a u H).norm.aestronglyMeasurable
  have hdom := hi.const_mul (Real.exp (2*(U+H)))
  have hleft : Integrable (fun x : ℝ=>Real.exp x*‖sharpWindow s a u H x‖) := by
    apply Integrable.mono' hdom (Real.continuous_exp.aestronglyMeasurable.mul hsm)
    filter_upwards [] with x
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
    exact exp_sharp_bound s a u hu x
  rw [←MeasureTheory.integral_const_mul]
  exact integral_mono hleft hdom (exp_sharp_bound s a u hu)

end OrdinarySharpWindow

end

end OAI
