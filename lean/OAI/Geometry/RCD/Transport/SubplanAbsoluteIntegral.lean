import Mathlib.MeasureTheory.Function.AEEqOfIntegral

namespace OAI

/-! # Absolute errors from normalized submeasure mean bounds -/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem integral_abs_le_of_setIntegral_bound (μ : Measure X) {f : X → ℝ}
    (hm : Measurable f) (hi : Integrable f μ) {C : ℝ}
    (hbound : ∀ S, MeasurableSet S → |∫ x in S, f x ∂μ|≤C) :
    (∫ x, |f x| ∂μ)≤2*C := by
  let S := {x | 0≤f x}
  have hS : MeasurableSet S := measurableSet_le measurable_const hm
  have hpos : (∫ x in S, |f x| ∂μ)=∫ x in S, f x ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hS] with x hx
    exact abs_of_nonneg hx
  have hneg : (∫ x in Sᶜ, |f x| ∂μ)=-(∫ x in Sᶜ, f x ∂μ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hS.compl] with x hx
    exact abs_of_nonpos (le_of_lt (not_le.mp hx))
  rw [← integral_add_compl hS hi.abs,hpos,hneg]
  have h1 := hbound S hS
  have h2 := hbound Sᶜ hS.compl
  linarith [le_abs_self (∫ x in S, f x ∂μ),neg_le_abs (∫ x in Sᶜ, f x ∂μ)]

theorem integral_abs_le_of_normalized_submeans (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hm : Measurable f) (hi : Integrable f μ) {C : ℝ} (hC : 0≤C)
    (hmean : ∀ κ : Measure X, κ≤μ → κ univ≠0 →
      |∫ x, f x ∂((κ univ)⁻¹ • κ)|≤((κ univ)⁻¹).toReal*C) :
    (∫ x, |f x| ∂μ)≤2*C := by
  apply integral_abs_le_of_setIntegral_bound μ hm hi
  intro S _hS
  by_cases hzero : μ S=0
  · rw [Measure.restrict_eq_zero.mpr hzero]
    simpa only [integral_zero_measure,abs_zero] using hC
  let κ := μ.restrict S
  have hk0 : κ univ≠0 := by simpa only [κ,Measure.restrict_apply_univ] using hzero
  have hkt : κ univ≠∞ := measure_ne_top κ univ
  have ha : 0<((κ univ)⁻¹).toReal := ENNReal.toReal_pos
    (ENNReal.inv_ne_zero.mpr hkt) (ENNReal.inv_ne_top.mpr hk0)
  have hh := hmean κ Measure.restrict_le_self hk0
  rw [integral_smul_measure,smul_eq_mul,abs_mul,abs_of_pos ha] at hh
  exact (mul_le_mul_iff_right₀ ha).mp hh

end RegularPointCoordinates

end

end OAI
