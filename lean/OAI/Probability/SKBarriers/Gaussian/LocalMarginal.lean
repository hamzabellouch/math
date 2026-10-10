import Mathlib
import OAI.Probability.SKBarriers.Calculus.MarginalSecondDerivative
import OAI.Probability.SKBarriers.Gaussian.LocalGaussian

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section LocalMarginalDerivatives
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_local_gaussian_integral (f : E × ℝ → F) (hf : ContDiff ℝ 1 f)
    (hg : GaussianLocallyDominated f) (hg₁ : GaussianLocallyDominated (fderiv ℝ f)) (x : E) :
    fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) x =
      ∫ y, leftRestrict (fderiv ℝ f (x,y)) ∂gaussianReal 0 1 := by
  exact (hasFDerivAt_local_gaussian_integral f _ hf.continuous
    (leftRestrict.continuous.comp ((hf.fderiv_right (m := 0) (by norm_num)).continuous))
    hg (hg₁.clm leftRestrict)
    (leftRestrict_hasFDerivAt f (hf.differentiable (by norm_num))) x).fderiv

theorem norm_fderiv_local_gaussian_integral_le (f : E × ℝ → F) (hf : ContDiff ℝ 1 f)
    (hg : GaussianLocallyDominated f) (hg₁ : GaussianLocallyDominated (fderiv ℝ f)) (x : E) :
    ‖fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) x‖ ≤
      ∫ y, ‖fderiv ℝ f (x,y)‖ ∂gaussianReal 0 1 := by
  rw [fderiv_local_gaussian_integral f hf hg hg₁ x]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono
  · exact ((hg₁.clm leftRestrict).integrable_section
      (leftRestrict.continuous.comp ((hf.fderiv_right (m := 0) (by norm_num)).continuous)) x).norm
  · exact (hg₁.integrable_section ((hf.fderiv_right (m := 0) (by norm_num)).continuous) x).norm
  · exact fun y => leftRestrict_apply_bound _

end LocalMarginalDerivatives
section LocalSecondMarginal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem secondLeftRestrict_local_growth {f : E × ℝ → ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)}
    (hg : GaussianLocallyDominated f) : GaussianLocallyDominated (fun x => secondLeftRestrict (f x)) := by
  exact hg.of_norm_le zero_le_one (fun point =>
    (secondLeftRestrict_apply_bound (f point)).trans_eq (one_mul _).symm)

theorem fderiv_fderiv_local_gaussian_integral (f : E × ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : GaussianLocallyDominated f) (hg₁ : GaussianLocallyDominated (fderiv ℝ f))
    (hg₂ : GaussianLocallyDominated (fderiv ℝ (fderiv ℝ f))) (x : E) :
    fderiv ℝ (fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1)) x =
      ∫ y, secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (x,y)) ∂gaussianReal 0 1 := by
  have he : fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) =
      fun x => ∫ y, leftRestrict (fderiv ℝ f (x,y)) ∂gaussianReal 0 1 := by
    funext x
    exact fderiv_local_gaussian_integral f (hf.of_le (by norm_num)) hg hg₁ x
  rw [he]
  let T : ((E × ℝ) →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := leftRestrict
  have hd : ∀ a b, HasFDerivAt (fun z => T (fderiv ℝ f (z,b)))
      (secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (a,b))) a := by
    intro a b
    have h₁ := T.hasFDerivAt.comp (a,b)
      ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) (a,b)).hasFDerivAt
    have hxy : HasFDerivAt (fun z : E => (z,b)) (ContinuousLinearMap.inl ℝ E ℝ) a :=
      (hasFDerivAt_id a).prodMk (hasFDerivAt_const b a)
    convert! h₁.comp a hxy using 1
  apply (hasFDerivAt_local_gaussian_integral (fun z => T (fderiv ℝ f z)) _
    (T.continuous.comp (hf.fderiv_right (m := 1) (by norm_num)).continuous)
    (secondLeftRestrict.continuous.comp (hf.fderiv_right (m := 1) (by norm_num)
      |>.fderiv_right (m := 0) (by norm_num)).continuous)
    (hg₁.clm T) (secondLeftRestrict_local_growth hg₂) hd x).fderiv

theorem norm_fderiv_fderiv_local_gaussian_integral_le (f : E × ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : GaussianLocallyDominated f) (hg₁ : GaussianLocallyDominated (fderiv ℝ f))
    (hg₂ : GaussianLocallyDominated (fderiv ℝ (fderiv ℝ f))) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1)) x‖ ≤
      ∫ y, ‖fderiv ℝ (fderiv ℝ f) (x,y)‖ ∂gaussianReal 0 1 := by
  rw [fderiv_fderiv_local_gaussian_integral f hf hg hg₁ hg₂ x]
  apply (norm_integral_le_integral_norm _).trans
  have hc := (hf.fderiv_right (m := 1) (by norm_num) |>.fderiv_right (m := 0) (by norm_num)).continuous
  apply integral_mono_of_nonneg (ae_of_all _ (fun y =>
    ContinuousLinearMap.opNorm_nonneg (secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (x,y)))))
  · exact (hg₂.integrable_section hc x).norm
  · exact ae_of_all _ (fun y => secondLeftRestrict_apply_bound _)

end LocalSecondMarginal
end SK.Analytic

end
end

end

end OAI
