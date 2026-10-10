import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.DisorderPairs

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def gaussianPair : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)
instance gaussianPair_probability : IsProbabilityMeasure gaussianPair := by
  unfold gaussianPair; infer_instance

theorem gaussianPair_fst : HasLaw (Prod.fst : ℝ × ℝ → ℝ) (gaussianReal 0 1) gaussianPair :=
  measurePreserving_fst.hasLaw

theorem gaussianPair_snd : HasLaw (Prod.snd : ℝ × ℝ → ℝ) (gaussianReal 0 1) gaussianPair :=
  measurePreserving_snd.hasLaw

theorem gaussianPair_independent : IndepFun (Prod.fst : ℝ × ℝ → ℝ) Prod.snd gaussianPair := by
  exact (indepFun_iff_hasLaw_prodMk_prod gaussianPair_fst gaussianPair_snd).2 HasLaw.id

theorem gaussianPair_gaussian : HasGaussianLaw (fun p : ℝ × ℝ => p) gaussianPair :=
  gaussianPair_independent.hasGaussianLaw gaussianPair_fst.hasGaussianLaw gaussianPair_snd.hasGaussianLaw

def gaussianMix (a b : ℝ) (p : ℝ × ℝ) : ℝ := a*p.1+b*p.2

def gaussianMixCLM (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ+b • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem gaussianMix_gaussian (a b : ℝ) : HasGaussianLaw (gaussianMix a b) gaussianPair :=
  gaussianPair_gaussian.map_fun (gaussianMixCLM a b)

theorem gaussianMix_mean (a b : ℝ) : (∫ p, gaussianMix a b p ∂gaussianPair)=0 := by
  unfold gaussianMix
  rw [integral_add (gaussianPair_fst.hasGaussianLaw.integrable.const_mul a)
    (gaussianPair_snd.hasGaussianLaw.integrable.const_mul b),integral_const_mul,integral_const_mul]
  have hf := gaussianPair_fst.integral_comp (continuous_id.aestronglyMeasurable)
  have hs := gaussianPair_snd.integral_comp (continuous_id.aestronglyMeasurable)
  simp only [Function.comp_def,id_eq,integral_id_gaussianReal] at hf hs
  rw [hf,hs]; ring

theorem gaussianMix_covariance (a b c d : ℝ) :
    cov[gaussianMix a b,gaussianMix c d;gaussianPair]=a*c+b*d := by
  have hcross : cov[(Prod.fst : ℝ × ℝ → ℝ),Prod.snd;gaussianPair]=0 :=
    gaussianPair_independent.covariance_eq_zero gaussianPair_fst.hasGaussianLaw.memLp_two
      gaussianPair_snd.hasGaussianLaw.memLp_two
  have hf : cov[(Prod.fst : ℝ × ℝ → ℝ),Prod.fst;gaussianPair]=1 := by
    rw [covariance_self gaussianPair_fst.aemeasurable]
    have H := gaussianPair_fst.variance_eq
    simpa only [variance_id_gaussianReal,NNReal.coe_one] using H
  have hs : cov[(Prod.snd : ℝ × ℝ → ℝ),Prod.snd;gaussianPair]=1 := by
    rw [covariance_self gaussianPair_snd.aemeasurable]
    have H := gaussianPair_snd.variance_eq
    simpa only [variance_id_gaussianReal,NNReal.coe_one] using H
  unfold gaussianMix
  rw [SK.covariance_linear_combination gaussianPair_fst.hasGaussianLaw.memLp_two
    gaussianPair_snd.hasGaussianLaw.memLp_two gaussianPair_fst.hasGaussianLaw.memLp_two
    gaussianPair_snd.hasGaussianLaw.memLp_two,hf,hs,hcross,covariance_comm Prod.snd,hcross]
  ring

theorem gaussianMix_law (a b : ℝ) (hab : a^2+b^2=1) :
    HasLaw (gaussianMix a b) (gaussianReal 0 1) gaussianPair := by
  have hg := gaussianMix_gaussian a b
  refine ⟨hg.aemeasurable,?_⟩
  rw [hg.map_eq_gaussianReal,gaussianMix_mean,← covariance_self hg.aemeasurable,
    gaussianMix_covariance]
  have he : a*a+b*b=1 := by nlinarith [hab]
  rw [he]; norm_num

def gaussianRotate (θ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (gaussianMix (Real.cos θ) (Real.sin θ) p,
    gaussianMix (-Real.sin θ) (Real.cos θ) p)

theorem gaussianRotate_law (θ : ℝ) : HasLaw (gaussianRotate θ) gaussianPair gaussianPair := by
  have hg : HasGaussianLaw (gaussianRotate θ) gaussianPair :=
    gaussianPair_gaussian.map_fun ((gaussianMixCLM (Real.cos θ) (Real.sin θ)).prod
      (gaussianMixCLM (-Real.sin θ) (Real.cos θ)))
  have hi := hg.indepFun_of_covariance_eq_zero (by rw [gaussianMix_covariance]; ring)
  exact hi.hasLaw_prod
    (gaussianMix_law _ _ (by nlinarith [Real.sin_sq_add_cos_sq θ]))
    (gaussianMix_law _ _ (by nlinarith [Real.sin_sq_add_cos_sq θ]))

theorem gaussianRotate_inverse (θ : ℝ) (p : ℝ × ℝ) :
    gaussianRotate (-θ) (gaussianRotate θ p)=p := by
  ext <;> simp only [gaussianRotate,gaussianMix,Real.cos_neg,Real.sin_neg]
  · calc
      _=(Real.sin θ^2+Real.cos θ^2)*p.1 := by ring
      _=p.1 := by rw [Real.sin_sq_add_cos_sq]; ring
  · calc
      _=(Real.sin θ^2+Real.cos θ^2)*p.2 := by ring
      _=p.2 := by rw [Real.sin_sq_add_cos_sq]; ring

end SK.Analytic

end
end

end OAI
