import Mathlib
import OAI.Probability.SKSupport.Control.ValueDifference

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat

lemma convex_gradient_comparison {f g : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    (hg : ConvexOn ℝ univ g) (hfd : Differentiable ℝ f) (hgd : Differentiable ℝ g)
    {L : ℝ≥0} (hL : LipschitzWith L (deriv g)) {E : ℝ} (hE : ∀ x, |f x-g x| ≤ E)
    {h : ℝ} (hh : 0 < h) (x : ℝ) :
    |deriv f x-deriv g x| ≤ 2*E/h+(L:ℝ)*h := by
  have hfU := hf.deriv_le_slope (mem_univ x) (mem_univ (x+h)) (by linarith) (hfd x)
  have hfL := hf.slope_le_deriv (mem_univ (x-h)) (mem_univ x) (by linarith) (hfd x)
  have hgU := hg.slope_le_deriv (mem_univ x) (mem_univ (x+h)) (by linarith) (hgd (x+h))
  have hgL := hg.deriv_le_slope (mem_univ (x-h)) (mem_univ x) (by linarith) (hgd (x-h))
  have hplus := hL.dist_le_mul (x+h) x
  have hminus := hL.dist_le_mul (x-h) x
  rw [Real.dist_eq,Real.dist_eq,add_sub_cancel_left,abs_of_pos hh] at hplus
  rw [Real.dist_eq,Real.dist_eq,sub_sub_cancel_left,abs_neg,abs_of_pos hh] at hminus
  have e0 := (abs_le.mp (hE x))
  have e1 := (abs_le.mp (hE (x+h)))
  have e2 := (abs_le.mp (hE (x-h)))
  have hp := abs_le.mp hplus
  have hm := abs_le.mp hminus
  simp only [slope_def_field,add_sub_cancel_left,sub_sub_cancel] at hfU hfL hgU hgL
  have hFU := (le_div_iff₀ hh).mp hfU
  have hFL := (div_le_iff₀ hh).mp hfL
  have hGU := (div_le_iff₀ hh).mp hgU
  have hGL := (le_div_iff₀ hh).mp hgL
  apply abs_le.mpr
  constructor <;> apply (mul_le_mul_iff_right₀ hh).mp
  · have hdiv : (2*E/h)*h=2*E := div_mul_cancel₀ _ hh.ne'
    nlinarith [mul_le_mul_of_nonneg_right hm.1 hh.le]
  · have hdiv : (2*E/h)*h=2*E := div_mul_cancel₀ _ hh.ne'
    nlinarith [mul_le_mul_of_nonneg_right hp.2 hh.le]

variable {Ω : Type*} [MeasurableSpace Ω]

lemma compactGradient_stability (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) :
    ∃ L : ℝ≥0, ∀ β : OrderParameter, ∀ h > 0, ∀ t x,
      |compactGradient W β T t x-compactGradient W γ T t x| ≤
        3*coefficientDistance β γ/h+(L:ℝ)*h := by
  obtain ⟨L,hL⟩ := compactGradient_lipschitz W γ T.property.1 T.property.2
  refine ⟨L,fun β h hh t x => ?_⟩
  have ht0 := (stripClamp_mem T.property.1 t).1
  have ht1 := (stripClamp_mem T.property.1 t).2.trans_lt T.property.2
  have hg : LipschitzWith L (deriv (value W γ (stripClamp T t))) := hL t
  have hb := convex_gradient_comparison (value_convex W β _ ht1.le)
    (value_convex W γ _ ht1.le)
    ((value_contDiff W β ht0 ht1).differentiable (by simp))
    ((value_contDiff W γ ht0 ht1).differentiable (by simp)) hg
    (fun y => value_difference_bound W β γ ht0 ht1.le y) hh x
  change |deriv (value W β (stripClamp T t)) x-deriv (value W γ (stripClamp T t)) x| ≤ _
  convert hb using 1
  ring

end ZeroTemperatureSK

end
end

end OAI
