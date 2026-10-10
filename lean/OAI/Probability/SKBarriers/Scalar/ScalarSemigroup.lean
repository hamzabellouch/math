import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarMassOne

namespace OAI

section

noncomputable section
open scoped NNReal
open MeasureTheory ProbabilityTheory
namespace SK.Analytic

theorem integral_gaussian_mul (v : ℝ) {g : ℝ → ℝ} (hg : StronglyMeasurable g) :
    (∫ y, g (v*y) ∂gaussianReal 0 1) =
      ∫ y, g y ∂gaussianReal 0 (NNReal.mk (v^2) (sq_nonneg v)) := by
  have hμ := gaussianReal_map_const_mul (μ := 0) (v := 1) v
  simp only [mul_zero,mul_one] at hμ
  rw [← hμ,integral_map (by fun_prop) hg.aestronglyMeasurable]

theorem integral_gaussian_sum {g : ℝ → ℝ} (hg : Continuous g) (hG : HasExpGrowth g)
    (v w a : ℝ) (ha : a^2=v^2+w^2) :
    (∫ y, ∫ z, g (v*y+w*z) ∂gaussianReal 0 1 ∂gaussianReal 0 1) =
      ∫ y, g (a*y) ∂gaussianReal 0 1 := by
  let V : ℝ≥0 := NNReal.mk (v^2) (sq_nonneg v)
  let W : ℝ≥0 := NNReal.mk (w^2) (sq_nonneg w)
  let A : ℝ≥0 := NNReal.mk (a^2) (sq_nonneg a)
  have he : V+W=A := NNReal.eq ha.symm
  have hint : Integrable g ((gaussianReal 0 V) ∗ (gaussianReal 0 W)) := by
    rw [gaussianReal_conv_gaussianReal,zero_add]
    exact hG.integrable_gaussianMeasure hg
  have H := integral_conv hint
  rw [gaussianReal_conv_gaussianReal,zero_add,he] at H
  have hb (y : ℝ) : (∫ z, g (v*y+w*z) ∂gaussianReal 0 1) =
      ∫ z, g (v*y+z) ∂gaussianReal 0 W :=
    integral_gaussian_mul w (hg.comp (continuous_const.add continuous_id)).stronglyMeasurable
  simp_rw [hb]
  have hsm : StronglyMeasurable (fun t => ∫ z, g (t+z) ∂gaussianReal 0 W) :=
    (hg.comp (continuous_fst.add continuous_snd)).stronglyMeasurable.integral_prod_right'
  rw [integral_gaussian_mul v hsm,← H]
  exact (integral_gaussian_mul a hg.stronglyMeasurable).symm

theorem exp_mul_scalarStep {f : ℝ → ℝ} (hf : BoundedDerivs f) {m : ℝ}
    (hm : m ≠ 0) (v x : ℝ) :
    Real.exp (m*scalarStep m v f x) =
      ∫ y, Real.exp (m*f (x+v*y)) ∂gaussianReal 0 1 := by
  have hi : Integrable (fun y => Real.exp (m*f (x+v*y))) (gaussianReal 0 1) := by
    let L : ℝ →L[ℝ] ℝ := v • ContinuousLinearMap.id ℝ ℝ
    exact (((hf.translate x).compCLM L).exp_growths m).1.integrable_gaussianMeasure
      (Real.continuous_exp.comp (continuous_const.mul (hf.1.continuous.comp
        (continuous_const.add (continuous_const.mul continuous_id)))))
  simp only [scalarStep,gaussianStep,ite_eq_right hm,positiveGaussianLogStep]
  rw [mul_div_cancel₀ _ hm,Real.exp_log (integral_exp_pos hi)]

theorem scalarStep_semigroup {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (m v w a : ℝ) (ha : a^2=v^2+w^2) :
    scalarStep m v (scalarStep m w f) = scalarStep m a f := by
  funext x
  by_cases hm : m=0
  · subst m
    simp only [scalarStep,gaussianStep,ite_true]
    have H := integral_gaussian_sum (hf.translate x).1.continuous
      (hf.translate x).hasExpGrowth v w a ha
    simpa only [add_assoc, Function.comp_apply, Pi.mul_apply] using H
  · apply (mul_left_cancel₀ hm)
    apply Real.exp_injective
    rw [exp_mul_scalarStep (scalarStep_regular hf m w) hm,exp_mul_scalarStep hf hm]
    simp_rw [exp_mul_scalarStep hf hm]
    have H := integral_gaussian_sum
      (Real.continuous_exp.comp (continuous_const.mul (hf.translate x).1.continuous))
      ((hf.translate x).exp_growths m).1 v w a ha
    simpa only [add_assoc, Function.comp_apply, Pi.mul_apply] using H

end SK.Analytic

end
end

end OAI
