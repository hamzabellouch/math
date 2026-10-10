import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianAverage
import OAI.Probability.SKBarriers.Calculus.ParameterAlgebra
import OAI.Probability.SKBarriers.Calculus.ParameterProduct
import OAI.Probability.SKBarriers.Calculus.ParameterRecursion

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section ParameterAverage
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ParamRegular.exp_gaussian_pos {f : P × (E × ℝ) → ℝ}
    (hf : ParamRegular f) (m : ℝ) (z : P × E) :
    0 < ∫ y, Real.exp (m*f (z.1,(z.2,y))) ∂gaussianReal 0 1 := by
  apply integral_exp_pos
  exact (hf.2.1.exp_mul m).weakLocallyDominated.integrable_section
    (Real.continuous_exp.comp (continuous_const.mul (hf.1.continuous.comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))))) z

theorem ParamSmooth.gaussianAverage {f g : P × (E × ℝ) → ℝ}
    (hf : ParamRegular f) (hg : ParamSmooth g) (m : ℝ) :
    ParamSmooth (SK.Analytic.gaussianAverage m
      (fun z : (P × E) × ℝ => f (z.1.1,(z.1.2,z.2)))
      (fun z : (P × E) × ℝ => g (z.1.1,(z.1.2,z.2)))) := by
  have hZ := (((hf.const_mul m).log_gaussian_exp).const_mul (-1)).expSmooth
  have hN := ((hf.const_mul m).expSmooth.mul hg).gaussian_integral
  have he : SK.Analytic.gaussianAverage m
      (fun z : (P × E) × ℝ => f (z.1.1,(z.1.2,z.2)))
      (fun z : (P × E) × ℝ => g (z.1.1,(z.1.2,z.2))) = fun z : P × E =>
      Real.exp (-1*Real.log (∫ y, Real.exp (m*f (z.1,(z.2,y))) ∂gaussianReal 0 1))*
      (∫ y, Real.exp (m*f (z.1,(z.2,y)))*g (z.1,(z.2,y)) ∂gaussianReal 0 1) := by
    funext z
    rw [neg_one_mul,Real.exp_neg,Real.exp_log (hf.exp_gaussian_pos m z)]
    exact gaussianStepLaw_integral_inv_smul m _ z _
  rw [he]
  exact hZ.mul hN
end ParameterAverage
end SK.Analytic

end
end

end

end OAI
