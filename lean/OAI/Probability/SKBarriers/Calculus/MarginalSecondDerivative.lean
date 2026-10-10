import Mathlib
import OAI.Probability.SKBarriers.Gaussian.ExponentialGrowth
import OAI.Probability.SKBarriers.Calculus.MarginalDerivatives

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section SecondMarginal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def secondLeftRestrict :
    ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  leftRestrict ∘L
    ((ContinuousLinearMap.compL ℝ (E × ℝ) ((E × ℝ) →L[ℝ] ℝ) (E →L[ℝ] ℝ)) leftRestrict)

theorem secondLeftRestrict_apply_bound (B : (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ) :
    ‖secondLeftRestrict B‖ ≤ ‖B‖ := by
  apply (leftRestrict_apply_bound _).trans
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right leftRestrict_norm (norm_nonneg B)).trans_eq (one_mul _))

theorem secondLeftRestrict_growth {f : E × ℝ → ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)}
    (hg : HasExpGrowth f) : HasExpGrowth (fun x => secondLeftRestrict (f x)) := by
  exact hg.congr_bound zero_le_one (fun x =>
    (secondLeftRestrict_apply_bound _).trans_eq (one_mul _).symm)

theorem fderiv_fderiv_gaussian_integral (f : E × ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : HasExpGrowth f) (hg₁ : HasExpGrowth (fderiv ℝ f))
    (hg₂ : HasExpGrowth (fderiv ℝ (fderiv ℝ f))) (x : E) :
    fderiv ℝ (fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1)) x =
      ∫ y, secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (x,y)) ∂gaussianReal 0 1 := by
  have he : fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) =
      fun x => ∫ y, leftRestrict (fderiv ℝ f (x,y)) ∂gaussianReal 0 1 := by
    funext x
    exact fderiv_gaussian_integral f (hf.of_le (by norm_num)) hg hg₁ x
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
  apply (hasFDerivAt_gaussian_integral (fun z => T (fderiv ℝ f z)) _
    (T.continuous.comp (hf.fderiv_right (m := 1) (by norm_num)).continuous)
    (secondLeftRestrict.continuous.comp (hf.fderiv_right (m := 1) (by norm_num)
      |>.fderiv_right (m := 0) (by norm_num)).continuous)
    (hg₁.clm T) (secondLeftRestrict_growth hg₂) hd x).fderiv

theorem norm_fderiv_fderiv_gaussian_integral_le (f : E × ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : HasExpGrowth f) (hg₁ : HasExpGrowth (fderiv ℝ f))
    (hg₂ : HasExpGrowth (fderiv ℝ (fderiv ℝ f))) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1)) x‖ ≤
      ∫ y, ‖fderiv ℝ (fderiv ℝ f) (x,y)‖ ∂gaussianReal 0 1 := by
  rw [fderiv_fderiv_gaussian_integral f hf hg hg₁ hg₂ x]
  apply (norm_integral_le_integral_norm _).trans
  have hc := (hf.fderiv_right (m := 1) (by norm_num) |>.fderiv_right (m := 0) (by norm_num)).continuous
  apply integral_mono_of_nonneg (ae_of_all _ (fun y =>
    ContinuousLinearMap.opNorm_nonneg (secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (x,y)))))
  · exact (hg₂.norm (fun z => ContinuousLinearMap.opNorm_nonneg _)).integrable_gaussian_section hc.norm x
  · exact ae_of_all _ (fun y => secondLeftRestrict_apply_bound _)

end SecondMarginal
end SK.Analytic

end
end
end
end
end
end

end OAI
