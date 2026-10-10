import OAI.Probability.InvariantIsing.Fields.FieldGaussianSemigroup
import OAI.Probability.InvariantIsing.Magnetic.MagneticScalarSlab

namespace OAI

/-! At exponent one the Gaussian log-cosh operator adds only a constant.
This is the terminal endpoint of the adjacent-variance comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldGaussian_integral_cosh (v : ℝ≥0) (z : ℝ) :
    (∫ y, Real.cosh y ∂gaussianReal z v) = Real.exp (v / 2) * Real.cosh z := by
  have hp : (∫ y, Real.exp y ∂gaussianReal z v) = Real.exp (z + v / 2) := by
    simpa only [mgf, one_mul, mul_one, one_pow] using
      congrFun (mgf_fun_id_gaussianReal (μ := z) (v := v)) 1
  have hn : (∫ y, Real.exp (-y) ∂gaussianReal z v) = Real.exp (-z + v / 2) := by
    simpa only [mgf, neg_one_mul, mul_neg_one, neg_one_sq, mul_one] using
      congrFun (mgf_fun_id_gaussianReal (μ := z) (v := v)) (-1)
  have hip : Integrable (fun y => Real.exp y) (gaussianReal z v) := by
    simpa only [one_mul] using integrable_exp_mul_gaussianReal (μ := z) (v := v) 1
  have hin : Integrable (fun y => Real.exp (-y)) (gaussianReal z v) := by
    simpa only [neg_one_mul] using integrable_exp_mul_gaussianReal (μ := z) (v := v) (-1)
  simp only [Real.cosh_eq, integral_div, integral_add hip hin, hp, hn, Real.exp_add]
  ring

lemma gaussianOperator_one_logCosh (v : ℝ≥0) (z : ℝ) :
    gaussianOperator 1 v (fun y => Real.log (Real.cosh y)) z =
      v / 2 + Real.log (Real.cosh z) := by
  rw [gaussianOperator_eq_gaussian_exp_integral (by norm_num) v measurable_logCosh z]
  simp only [one_mul, inv_one]
  have he : (fun y : ℝ => Real.exp (Real.log (Real.cosh y))) = Real.cosh := by
    funext y
    exact Real.exp_log (Real.cosh_pos y)
  rw [he, fieldGaussian_integral_cosh, Real.log_mul (Real.exp_ne_zero _)
    (Real.cosh_pos z).ne', Real.log_exp]

lemma fieldSpinTransition_one_tanh (v : ℝ≥0) (z : ℝ) :
    fieldSpinTransition 1 v (fun y => Real.log (Real.cosh y)) Real.tanh z =
      Real.tanh z := by
  have hnil : ∀ av ∈ ([] : List (ℝ × ℝ≥0)), 0 < av.1 := by simp
  have hd := magneticScalarSlab_value_hasDerivAt [] hnil 1 (v : ℝ) z
  have he : gaussianOperator 1 v (fun y => Real.log (Real.cosh y)) =
      (fun y => v / 2 + Real.log (Real.cosh y)) :=
    funext (gaussianOperator_one_logCosh v)
  have ht : HasDerivAt (fun y => v / 2 + Real.log (Real.cosh y)) (Real.tanh z) z := by
    simpa only [Real.tanh_eq_sinh_div_cosh] using
      ((Real.hasDerivAt_cosh z).log (Real.cosh_pos z).ne').const_add ((v : ℝ) / 2)
  change HasDerivAt (gaussianOperator 1 (Real.toNNReal (v : ℝ))
    (fun y => Real.log (Real.cosh y)))
    (fieldSpinTransition 1 (Real.toNNReal (v : ℝ))
      (fun y => Real.log (Real.cosh y)) Real.tanh z) z at hd
  rw [Real.toNNReal_coe, he] at hd
  exact hd.unique ht

lemma fieldSpinTransition_const_add (ζ : ℝ) (v : ℝ≥0) (F a : ℝ → ℝ)
    (c z : ℝ) :
    fieldSpinTransition ζ v (fun y => c + F y) a z = fieldSpinTransition ζ v F a z := by
  unfold fieldSpinTransition
  simp only [integral_tilted_eq_div, mul_add, Real.exp_add, mul_assoc,
    integral_const_mul]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

end InvariantIsing

end

end OAI
