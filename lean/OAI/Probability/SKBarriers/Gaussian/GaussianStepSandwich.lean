import Mathlib
import OAI.Probability.SKBarriers.Calculus.ParameterGrowth
import OAI.Probability.SKBarriers.Gaussian.ExponentialAverage
import OAI.Probability.SKBarriers.Gaussian.GaussianStepAlgebra

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem HasExpGrowth.integrable_gaussianStepLaw {f g : E × ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : HasExpGrowth g) (hc : Continuous g) (m : ℝ) (x : E) :
    Integrable (fun y => g (x,y)) (gaussianStepLaw m f x) := by
  rw [gaussianStepLaw,integrable_tilted_iff (hf.exp_integrable m x)]
  exact (((hf.exp_growths m).1).smul hg).integrable_gaussian_section
    ((Real.continuous_exp.comp (continuous_const.mul hf.1.continuous)).smul hc) x

theorem exp_gaussianStep {f : E × ℝ → ℝ} (hf : BoundedDerivs f) (m : ℝ) (x : E) :
    Real.exp (m*gaussianStep m f x)=∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1 := by
  by_cases hm : m=0
  · simp [hm]
  · rw [gaussianStep,ite_eq_right hm,positiveGaussianLogStep]
    rw [mul_div_cancel₀ _ hm,Real.exp_log (integral_exp_pos (hf.exp_integrable m x))]

theorem gaussianAverage_exp_increment {f g : E × ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) (m : ℝ) (x : E) :
    gaussianAverage m f (fun z => Real.exp (m*(g z-f z))) x=
      Real.exp (m*(gaussianStep m g x-gaussianStep m f x)) := by
  rw [gaussianAverage_exp_representation hf]
  simp only [smul_eq_mul]
  have he (y : ℝ) : Real.exp (m*f (x,y))*Real.exp (m*(g (x,y)-f (x,y)))=
      Real.exp (m*g (x,y)) := by rw [← Real.exp_add]; congr 1; ring
  simp_rw [he]
  rw [← exp_gaussianStep hg m x,← Real.exp_add]
  congr 1
  ring

theorem gaussianStep_increment_sandwich {f g : E × ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) {m : ℝ} (hm : m∈Icc (0:ℝ) 1) (x : E) :
    gaussianAverage m f (fun z => g z-f z) x ≤ gaussianStep m g x-gaussianStep m f x ∧
    Real.exp (gaussianStep m g x-gaussianStep m f x) ≤
      gaussianAverage m f (fun z => Real.exp (g z-f z)) x := by
  let ν := gaussianStepLaw m f x
  let U := fun z => g z-f z
  have hU : BoundedDerivs U := by simpa only [neg_one_mul, ← sub_eq_add_neg] using hg.add (hf.const_mul (-1))
  let := gaussianStepLaw_probability hf m x
  have hi : Integrable (fun y => U (x,y)) ν :=
    hU.hasExpGrowth.integrable_gaussianStepLaw hf hU.1.continuous m x
  have hiE (a : ℝ) : Integrable (fun y => Real.exp (a*U (x,y))) ν :=
    ((hU.exp_growths a).1).integrable_gaussianStepLaw hf
      (Real.continuous_exp.comp (continuous_const.mul hU.1.continuous)) m x
  have hi1 : Integrable (fun y => Real.exp (U (x,y))) ν := by simpa only [one_mul] using hiE 1
  have jensen (a : ℝ) : Real.exp (a*(∫ y, U (x,y) ∂ν)) ≤ ∫ y, Real.exp (a*U (x,y)) ∂ν := by
    have H := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (Eventually.of_forall (fun _ => mem_univ _)) (hi.const_mul a) (hiE a)
    simpa only [integral_const_mul] using H
  by_cases hz : m=0
  · subst m
    have he : gaussianStep 0 g x-gaussianStep 0 f x=∫ y, U (x,y) ∂ν := by
      simp only [ν,gaussianStepLaw_zero,gaussianStep,ite_true]
      exact (integral_sub (hg.hasExpGrowth.integrable_gaussian_section hg.1.continuous x) (hf.hasExpGrowth.integrable_gaussian_section hf.1.continuous x)).symm
    rw [he]
    constructor
    · exact le_rfl
    · simpa only [one_mul, gaussianAverage, U, ν] using jensen 1
  · have hm0 : 0 < m := lt_of_le_of_ne hm.1 (Ne.symm hz)
    have hident : (∫ y, Real.exp (m*U (x,y)) ∂ν)=
        Real.exp (m*(gaussianStep m g x-gaussianStep m f x)) := gaussianAverage_exp_increment hf hg m x
    have hl := jensen m
    rw [hident,Real.exp_le_exp] at hl
    refine ⟨(mul_le_mul_iff_right₀ hm0).mp hl,?_⟩
    let J := ∫ y, Real.exp (U (x,y)) ∂ν
    have hJ : 0 < J := integral_exp_pos hi1
    have hp : (∫ y, Real.exp (m*U (x,y)) ∂ν) ≤ J^m := by
      have heq : (fun y => (Real.exp (U (x,y)))^m)=fun y => Real.exp (m*U (x,y)) := by
        funext y
        rw [← Real.exp_mul,mul_comm]
      have H := (Real.concaveOn_rpow hm.1 hm.2).le_map_integral
        (Real.continuous_rpow_const hm.1).continuousOn isClosed_Ici
        (Eventually.of_forall (fun y => (Real.exp_pos (U (x,y))).le)) hi1 (by
          change Integrable (fun y => (Real.exp (U (x,y)))^m) ν
          rw [heq]
          exact hiE m)
      simpa only [heq] using H
    rw [hident,Real.rpow_def_of_pos hJ,Real.exp_le_exp] at hp
    have hu : gaussianStep m g x-gaussianStep m f x ≤ Real.log J := by nlinarith
    have H := Real.exp_le_exp.mpr hu
    rw [Real.exp_log hJ] at H
    exact H
end

end SK.Analytic

end
end

end OAI
