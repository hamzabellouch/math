import Mathlib
import OAI.Probability.GaussianInformation.Kernel.Sphere

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace EntropySupport
noncomputable def xlog (x : ℝ) : ℝ := x * Real.log x

lemma continuous_xlog : Continuous xlog := Real.continuous_mul_log
lemma xlog_zero : xlog 0 = 0 := by simp [xlog]
lemma xlog_one : xlog 1 = 0 := by simp [xlog]
lemma xlog_mul (x y : ℝ) : xlog (x*y) = y*xlog x+x*xlog y := by
  have h := Real.negMulLog_mul x y
  simp only [Real.negMulLog_def, neg_mul] at h
  dsimp [xlog]
  linarith

lemma mul_log_div_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x * Real.log (x/y) ≤ x^2/y-x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have h := Real.log_le_sub_one_of_pos (div_pos (lt_of_le_of_ne hx (Ne.symm hx0)) hy)
  have H := mul_le_mul_of_nonneg_left h hx
  simpa only [mul_sub, mul_one, pow_two, mul_div_assoc] using H

lemma xlog_lower_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    xlog y + (Real.log y+1)*(x-y) ≤ xlog x := by
  have h := Real.self_sub_one_le_mul_log (div_nonneg hx hy.le)
  by_cases hx0 : x = 0
  · simp only [hx0, xlog]
    nlinarith
  rw [Real.log_div hx0 hy.ne'] at h
  have H := mul_le_mul_of_nonneg_left h hy.le
  dsimp [xlog]
  field_simp at H
  nlinarith

lemma integrable_bounded_measurable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ := by
  apply Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, Function.comp_def] using hC x)

lemma integrable_xlog_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hf0 : ∀ x,0 ≤ f x) {M : ℝ} (hfM : ∀ x,f x ≤ M) : Integrable (fun x => xlog (f x)) μ := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc (a := (0:ℝ)) (b := M)).image continuous_xlog).isBounded.exists_norm_le
  apply integrable_bounded_measurable μ _ (continuous_xlog.measurable.comp hf)
  intro x
  simpa only [Real.norm_eq_abs,Function.comp_def] using hC _ (Set.mem_image_of_mem _ ⟨hf0 x,hfM x⟩)

lemma klDiv_withDensity_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hf0 : ∀ x,0 ≤ f x) {M : ℝ} (hfM : ∀ x,f x ≤ M)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))] :
    InformationTheory.klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ =
      ENNReal.ofReal (∫ x,xlog (f x) ∂μ) := by
  have hif := integrable_bounded_measurable μ f hf (fun x => by rw [abs_of_nonneg (hf0 x)]; exact hfM x)
  have hix := integrable_xlog_bounded μ f hf hf0 hfM
  have hib : Integrable (fun x => InformationTheory.klFun (f x)) μ :=
    (hix.add (integrable_const 1)).sub hif
  have hfint : ∫ x,f x ∂μ = 1 := by
    have h := measure_univ (μ := μ.withDensity (fun x => ENNReal.ofReal (f x)))
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hif (ae_of_all _ hf0)] at h
    exact (ENNReal.ofReal_eq_one.mp h)
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous μ _)]
  have hrn := Measure.rnDeriv_withDensity μ hf.ennreal_ofReal
  have he : (fun x => ENNReal.ofReal (InformationTheory.klFun (((μ.withDensity
      (fun x => ENNReal.ofReal (f x))).rnDeriv μ x).toReal))) =ᵐ[μ]
      (fun x => ENNReal.ofReal (InformationTheory.klFun (f x))) := by
    filter_upwards [hrn] with x hx
    rw [hx,ENNReal.toReal_ofReal (hf0 x)]
  rw [lintegral_congr_ae he,← ofReal_integral_eq_lintegral_ofReal hib
    (ae_of_all _ (fun x => InformationTheory.klFun_nonneg (hf0 x)))]
  congr 1
  change (∫ x,xlog (f x)+1-f x ∂μ) = _
  rw [integral_sub (f := fun x => xlog (f x)+1) (hix.add (integrable_const 1)) hif,
    integral_add hix (integrable_const 1),hfint]
  simp

end EntropySupport

end KernelPotential

end OAI
