import OAI.Probability.InvariantIsing.Gaussian.GaussianTiltIncrement
import OAI.Probability.InvariantIsing.Fields.FieldScalarDerivative
import OAI.Probability.InvariantIsing.Fields.FieldSpinSampling

namespace OAI

/-! Exponential moment bounds for the actual scalar canonical transition
kernels, including the unweighted root step. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarLogCosh_dist_le (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (x y : ℝ) :
    |fieldScalarValue L (fun z => Real.log (Real.cosh z)) x -
      fieldScalarValue L (fun z => Real.log (Real.cosh z)) y| ≤ |x - y| := by
  have hb := (fieldScalarMean_regular L hL measurable_logCosh logCosh_linearGrowth
    (by change Measurable (fun x : ℝ => Real.tanh x); simp only [Real.tanh_eq]; fun_prop)
    field_abs_tanh_le_one).2
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (univ : Set ℝ)) (C := 1)
    (fun z _ => (hasDerivAt_fieldScalarLogCosh L hL z).hasDerivWithinAt)
    (fun z _ => by simpa only [Real.norm_eq_abs] using hb z)
    convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using he

lemma fieldSpinTransition_exp_shift (v : ℝ≥0) (z b t : ℝ)
    (F : ℝ → ℝ) (hF : Measurable F) :
    fieldSpinTransition b v F (fun u => Real.exp (t * u)) z =
      Real.exp (t * z) * (∫ x, Real.exp (t * x)
        ∂(gaussianReal 0 v).tilted (fun x => b * F (z + x))) := by
  have hm : Measurable (fun u => Real.exp (b * F u) * Real.exp (t * u)) := by fun_prop
  rw [fieldSpinTransition, integral_tilted_eq_div, integral_tilted_eq_div,
    field_gaussian_integral_shift v z hm,
    field_gaussian_integral_shift v z (hF.const_mul b).exp]
  have he : (fun x : ℝ => Real.exp (b * F (z + x)) * Real.exp (t * (z + x))) =
      fun x => Real.exp (t * z) * (Real.exp (b * F (z + x)) * Real.exp (t * x)) := by
    funext x
    rw [mul_add, Real.exp_add]
    ring
  rw [he, integral_const_mul]
  ring

theorem fieldTransitionKernel_mgf (v : ℝ≥0) (z b t : ℝ)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (hLip : ∀ x y, |F x - F y| ≤ |x - y|) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (∫ u, Real.exp (t * u) ∂fieldTransitionKernel b v F hF z) ≤
      Real.exp (t * z + (t ^ 2 / 2 + |t|) * v) := by
  rw [fieldTransitionKernel_integral b v F hF hG,
    fieldSpinTransition_exp_shift v z b t F hF]
  have he := mul_le_mul_of_nonneg_left
    (gaussian_tilt_increment_mgf v z b t F hF hG hLip hb0 hb1) (Real.exp_pos (t * z)).le
  simpa only [Real.exp_add] using he

theorem fieldScalarTransition_mgf (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (v : ℝ≥0) (z b t : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    let hF := (fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth).1
    (∫ u, Real.exp (t * u)
      ∂fieldTransitionKernel b v (fieldScalarValue L (fun y => Real.log (Real.cosh y))) hF z) ≤
        Real.exp (t * z + (t ^ 2 / 2 + |t|) * v) :=
  fieldTransitionKernel_mgf v z b t _
    (fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth).1
    (fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth).2
    (fieldScalarLogCosh_dist_le L hL) hb0 hb1

end InvariantIsing

end

end OAI
