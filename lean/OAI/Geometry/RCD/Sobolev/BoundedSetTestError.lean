import OAI.Geometry.RCD.Sobolev.BoundedTestCutoffError

namespace OAI

/-! # Integral error is controlled by the symmetric difference of test domains -/

open Set MeasureTheory
open scoped symmDiff
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem bounded_set_test_error (μ : Measure X) [IsFiniteMeasure μ]
    {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t)
    {f : X → ℝ} (hf : Integrable f μ) {B : ℝ}
    (hb : ∀ᵐ x ∂μ, |f x|≤B) :
    |(∫ x in s, f x ∂μ)-(∫ x in t, f x ∂μ)|≤B*μ.real (s ∆ t) := by
  have hpoint : ∀ᵐ x ∂μ, ‖s.indicator f x-t.indicator f x‖≤
      B*(s ∆ t).indicator (fun _ => (1:ℝ)) x := by
    filter_upwards [hb] with x hx
    by_cases hxs : x∈s <;> by_cases hxt : x∈t
    all_goals simp only [mem_symmDiff,hxs,hxt,and_self,and_false,
      false_and,not_true_eq_false,not_false_eq_true,true_or,false_or,or_self,
      indicator_of_mem,indicator_of_notMem,sub_self,sub_zero,zero_sub,norm_neg,
      Real.norm_eq_abs,mul_one,mul_zero,abs_zero]
    all_goals first | exact hx | exact le_refl 0
  have hd : Integrable (fun x => s.indicator f x-t.indicator f x) μ :=
    (hf.indicator hs).sub (hf.indicator ht)
  have hi := (norm_integral_le_integral_norm (fun x => s.indicator f x-t.indicator f x)).trans
    (integral_mono_ae hd.norm (((integrable_const (1:ℝ)).indicator (hs.symmDiff ht)).const_mul B) hpoint)
  rw [integral_sub (hf.indicator hs) (hf.indicator ht),integral_indicator hs,
    integral_indicator ht,integral_const_mul,integral_indicator (hs.symmDiff ht),setIntegral_const] at hi
  simpa only [smul_eq_mul,mul_one,Real.norm_eq_abs] using hi

end RegularPointCoordinates

end

end OAI
