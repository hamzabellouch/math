import Mathlib

namespace OAI

section

open MeasureTheory Set Filter
open scoped ENNReal

namespace CAT0Fillings.RadialSobolev

lemma integral_cs_square {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b : α → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    (∫ x, a x*b x ∂μ)^2 ≤ (∫ x, (a x)^2 ∂μ)*(∫ x, (b x)^2 ∂μ) := by
  have hp : (2:ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hh := integral_mul_norm_le_Lp_mul_Lq hp (by simpa using ha) (by simpa using hb)
  have he (f : α → ℝ) : (fun x => ‖f x‖^(2:ℝ)) = (fun x => (f x)^2) := by
    funext x
    simp [Real.norm_eq_abs,sq_abs]
  rw [he a,he b,←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow] at hh
  have hi : |∫ x, a x*b x ∂μ| ≤ ∫ x, ‖a x‖*‖b x‖ ∂μ := by
    simpa only [Real.norm_eq_abs,abs_mul] using norm_integral_le_integral_norm (f := fun x => a x*b x) (μ := μ)
  have ha0 : 0 ≤ ∫ x, (a x)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hb0 : 0 ≤ ∫ x, (b x)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hbound := hi.trans hh
  have hs := sq_le_sq₀ (abs_nonneg (∫ x, a x*b x ∂μ))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) |>.mpr hbound
  simpa only [sq_abs,mul_pow,Real.sq_sqrt ha0,Real.sq_sqrt hb0] using hs

end CAT0Fillings.RadialSobolev
end

section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace CAT0Fillings.RadialSobolev

lemma continuous_memLp_Icc {h : ℝ → ℝ} (hh : Continuous h) (a b : ℝ) (p : ℝ≥0∞) :
    MemLp h p (volume.restrict (Icc a b)) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hh.continuousOn
  apply MemLp.of_bound hh.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC x hx

lemma continuous_mul_deriv_memLp_Icc {h f : ℝ → ℝ} {K : ℝ≥0}
    (hh : Continuous h) (hf : LipschitzWith K f) (a b : ℝ) (p : ℝ≥0∞) :
    MemLp (fun x => h x*deriv f x) p (volume.restrict (Icc a b)) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hh.continuousOn
  apply MemLp.of_bound (hh.aestronglyMeasurable.mul (measurable_deriv f).aestronglyMeasurable) (C*K)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  dsimp only [Pi.mul_apply]
  rw [norm_mul]
  exact mul_le_mul (hC x hx) (norm_deriv_le_of_lipschitz hf) (norm_nonneg _) ((norm_nonneg _).trans (hC x hx))

lemma weighted_interval_cs {w z f : ℝ → ℝ} {K : ℝ≥0} {a b : ℝ}
    (hab : a ≤ b) (hw : Continuous w) (hz : Continuous z) (hf : LipschitzWith K f)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) :
    (∫ x in a..b,w x*deriv f x*z x)^2 ≤
      (∫ x in a..b,w x*(deriv f x)^2)*(∫ x in a..b,w x*(z x)^2) := by
  have hs : Continuous (fun x => Real.sqrt (w x)) := hw.sqrt
  have hc := integral_cs_square
    (continuous_mul_deriv_memLp_Icc hs hf a b 2)
    (continuous_memLp_Icc (hs.mul hz) a b 2)
  dsimp only [Pi.mul_apply] at hc
  have ih : (∫ x in Icc a b, (Real.sqrt (w x)*deriv f x)*(Real.sqrt (w x)*z x)) =
      ∫ x in Icc a b,w x*deriv f x*z x := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    dsimp only
    have he := Real.sq_sqrt (hw0 x hx)
    calc
      _ = (Real.sqrt (w x))^2*deriv f x*z x := by ring
      _ = _ := by rw [he]
  have ie : (∫ x in Icc a b, (Real.sqrt (w x)*deriv f x)^2) =
      ∫ x in Icc a b,w x*(deriv f x)^2 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    dsimp only
    rw [mul_pow,Real.sq_sqrt (hw0 x hx)]
  have im : (∫ x in Icc a b, (Real.sqrt (w x)*z x)^2) =
      ∫ x in Icc a b,w x*(z x)^2 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    dsimp only
    rw [mul_pow,Real.sq_sqrt (hw0 x hx)]
  rw [ih,ie,im] at hc
  simpa only [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hab] using hc

end CAT0Fillings.RadialSobolev
end

end OAI
