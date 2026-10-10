import OAI.Analysis.CircleDomains.Sobolev.LocalZeroGradientConstant
import OAI.Analysis.CircleDomains.Sobolev.WeakHeightIdentification

namespace OAI

/-! The normalization of a zero-error height: its only possible freedom
is an additive constant, which exterior decay then removes. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def verticalLinear : EuclideanPlane →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp euclideanPlaneCoordinates.toContinuousLinearMap

 @[simp] theorem verticalLinear_apply (p : EuclideanPlane) : verticalLinear p = p 1 := rfl

 theorem vertical_translation_of_weak_gradient
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    (hw : DeGiorgi.HasWeakGrad (heightLimitGradient 0 0) v univ) :
    ∃ c : ℝ, ∀ p, v p = p 1+c := by
  have hY (i : Fin 2) : DeGiorgi.HasWeakPartialDeriv i
      (fun _ : EuclideanPlane => if i = 0 then 0 else 1) (fun p => p 1) univ := by
    have h := weakPartial_of_smooth_on isOpen_univ
      verticalLinear.contDiff.contDiffOn i
    convert h using 1
    · funext p
      fin_cases i <;> simp [ContinuousLinearMap.fderiv, verticalLinear_apply]
    · rfl
  have hw' (i : Fin 2) : DeGiorgi.HasWeakPartialDeriv i
      (fun _ : EuclideanPlane => if i = 0 then 0 else 1) v univ := by
    apply (hw i).congr_ae (Filter.EventuallyEq.rfl) ?_
    simp only [Measure.restrict_univ]
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure EuclideanPlane)] with p hp
    simp [heightLimitGradient]
  have hz : DeGiorgi.HasWeakGrad (fun _ => 0) (fun p => v p-p 1) univ := by
    intro i ψ hψ hs hsub
    have h0 := hw' i ψ hψ hs hsub
    have h1 := hY i ψ hψ hs hsub
    simp only [Measure.restrict_univ] at h0 h1 ⊢
    let t : EuclideanPlane → ℝ := fun p => fderiv ℝ ψ p (EuclideanSpace.single i 1)
    have ht : Continuous t := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hts : HasCompactSupport t := hs.fderiv_apply (𝕜 := ℝ) _
    have hvi : Integrable (fun p => v p*t p) volume := (hv.mul ht).integrable_of_hasCompactSupport hts.mul_left
    have hyi : Integrable (fun p => verticalLinear p*t p) volume := (verticalLinear.continuous.mul ht).integrable_of_hasCompactSupport hts.mul_left
    simp only [PiLp.zero_apply, zero_mul, integral_zero, neg_zero]
    simp_rw [sub_mul]
    change (∫ p, v p*t p-verticalLinear p*t p) = 0
    rw [integral_sub hvi hyi]
    change (∫ p, v p*t p)-(∫ p, p 1*t p) = 0
    exact sub_eq_zero.mpr (h0.trans h1.symm)
  obtain ⟨c, hc⟩ := constant_on_closure_of_zero_weak_gradient
    (hv.sub verticalLinear.continuous) (fun _ => 0) hz (fun _ _ => MemLp.zero)
    isOpen_univ isConnected_univ (Eventually.of_forall (fun _ => rfl))
  refine ⟨c, fun p => ?_⟩
  have h := hc p (by simp)
  change v p-p 1=c at h
  linarith

end CircleDomainRigidity

end

end OAI
