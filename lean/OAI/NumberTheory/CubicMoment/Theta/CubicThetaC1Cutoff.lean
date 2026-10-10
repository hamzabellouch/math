import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1EnergyLinear
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteEnergySum

namespace OAI

/-! Product bounds and local agreement for actual C1 section cutoffs. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

lemma cubicThetaSectionCutoff_regular (ψ : C(CubicThetaQuotient,ℂ))
    (hψ : ContDiffOn ℝ 1 (fun y => ψ (cubicThetaQuotientMap
      (cubicThetaPointInclusion.symm y))) {y : ℂ × ℝ | 0<y.2})
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    ContDiffOn ℝ 1 (cubicThetaSectionFunction (cubicThetaSectionCutoff ψ F))
      {y : ℂ × ℝ | 0<y.2} := hψ.mul hF

lemma cubicThetaSectionCutoff_gradient_error (ψ : C(CubicThetaQuotient,ℂ))
    (hψ : ContDiffOn ℝ 1 (fun y => ψ (cubicThetaQuotientMap
      (cubicThetaPointInclusion.symm y))) {y : ℂ × ℝ | 0<y.2})
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (p : CubicThetaPoint) :
    ‖cubicThetaSectionGradient (cubicThetaSectionCutoff ψ F) p-cubicThetaSectionGradient F p‖^2≤
      2*‖ψ (cubicThetaQuotientMap p)-1‖^2*‖cubicThetaSectionGradient F p‖^2+
      2*‖F.val p‖^2*(p.val.2^2*cubicThetaFunctionEnergy (fun y =>
        ψ (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))) p.val) := by
  let f := fun y => ψ (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))
  have hp : {y : ℂ × ℝ | 0<y.2}∈𝓝 p.val :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds p.property
  have hf : DifferentiableAt ℝ f p.val := (hψ.contDiffAt hp).differentiableAt (by simp)
  have hg := (hF.contDiffAt hp).differentiableAt (by simp)
  have hc := cubicThetaSectionCutoff_regular ψ hψ F hF
  rw [← cubicThetaC1Gradient_sub _ _ hc hF,cubicThetaSectionGradient_norm_sq]
  have he : cubicThetaSectionFunction (cubicThetaSectionCutoff ψ F-F)=
      (fun y => f y-1)*cubicThetaSectionFunction F := by
    funext y
    change f y*cubicThetaSectionFunction F y-cubicThetaSectionFunction F y=_
    simp only [Pi.mul_apply]
    ring
  have hdf : fderiv ℝ (fun y => f y-1) p.val=fderiv ℝ f p.val := by
    rw [fderiv_fun_sub hf (differentiableAt_const _),fderiv_const_apply,sub_zero]
  have hE : cubicThetaFunctionEnergy (fun y => f y-1) p.val=cubicThetaFunctionEnergy f p.val := by
    unfold cubicThetaFunctionEnergy
    rw [hdf]
  have hm := mul_le_mul_of_nonneg_left
    (cubicThetaFunctionEnergy_mul (hf.sub_const 1) hg) (sq_nonneg p.val.2)
  change p.val.2^2*cubicThetaFunctionEnergy (cubicThetaSectionFunction (cubicThetaSectionCutoff ψ F-F)) p.val≤_
  rw [he]
  rw [hE] at hm
  have hfv : f p.val=ψ (cubicThetaQuotientMap p) := by
    dsimp [f]
    have hl : cubicThetaPointInclusion.symm p.val=p :=
      cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
    exact congrArg (fun z => ψ (cubicThetaQuotientMap z)) hl
  have hgv : cubicThetaSectionFunction F p.val=F.val p :=
    cubicThetaSectionFunction_apply F p.property
  rw [hfv,hgv] at hm
  rw [cubicThetaSectionGradient_norm_sq]
  change _≤2*‖ψ (cubicThetaQuotientMap p)-1‖^2*
    (p.val.2^2*cubicThetaFunctionEnergy (cubicThetaSectionFunction F) p.val)+_
  nlinarith [hm]

lemma cubicThetaSectionCutoff_local_gradient (ψ : C(CubicThetaQuotient,ℂ))
    (F : CubicThetaSection) (p : CubicThetaPoint)
    (hψ : (ψ : CubicThetaQuotient → ℂ)=ᶠ[𝓝 (cubicThetaQuotientMap p)] (fun _ => 1)) :
    cubicThetaSectionGradient (cubicThetaSectionCutoff ψ F) p=cubicThetaSectionGradient F p := by
  have ht : p.val∈cubicThetaPointInclusion.target := by
    rw [cubicThetaPointInclusion_target]
    exact p.property
  have hm := cubicThetaQuotientMap_open.continuous.continuousAt.comp
    (cubicThetaPointInclusion.symm.continuousAt ht)
  have hleft : cubicThetaPointInclusion.symm p.val=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  change ContinuousAt (fun y => cubicThetaQuotientMap (cubicThetaPointInclusion.symm y)) p.val at hm
  have hmt : Tendsto (fun y => cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))
      (𝓝 p.val) (𝓝 (cubicThetaQuotientMap p)) := by
    simpa only [ContinuousAt,Function.comp_apply,hleft] using hm
  have he : cubicThetaSectionFunction (cubicThetaSectionCutoff ψ F)=ᶠ[𝓝 p.val]
      cubicThetaSectionFunction F := by
    filter_upwards [hψ.comp_tendsto hmt] with y hy
    change ψ (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))=1 at hy
    change ψ (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))*
      cubicThetaSectionFunction F y=cubicThetaSectionFunction F y
    rw [hy,one_mul]
  unfold cubicThetaSectionGradient cubicThetaSectionDifferential
  rw [he.fderiv_eq (𝕜:=ℝ)]

end CubicFirstMoment

end

end OAI
