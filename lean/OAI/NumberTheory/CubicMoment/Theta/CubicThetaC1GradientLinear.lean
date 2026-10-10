import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1EnergyLinear

namespace OAI

/-! Pointwise complex linearity of the actual differential on C1 sections. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaC1Gradient_add (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2}) (p : CubicThetaPoint) :
    cubicThetaSectionGradient (F+G) p=cubicThetaSectionGradient F p+cubicThetaSectionGradient G p := by
  have hp : {y : ℂ × ℝ | 0<y.2}∈nhds p.val :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds p.property
  have hdF := (hF.contDiffAt hp).differentiableAt (by simp)
  have hdG := (hG.contDiffAt hp).differentiableAt (by simp)
  have he : cubicThetaSectionFunction (F+G)=cubicThetaSectionFunction F+cubicThetaSectionFunction G := rfl
  ext i
  simp only [cubicThetaSectionGradient,cubicThetaSectionDifferential,he,fderiv_add hdF hdG,
    ContinuousLinearMap.comp_apply,add_apply,smul_add]
  rfl

lemma cubicThetaC1Gradient_smul (c : ℂ) (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) (p : CubicThetaPoint) :
    cubicThetaSectionGradient (c • F) p=c • cubicThetaSectionGradient F p := by
  have hp : {y : ℂ × ℝ | 0<y.2}∈nhds p.val :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds p.property
  have hdF := (hF.contDiffAt hp).differentiableAt (by simp)
  have he : cubicThetaSectionFunction (c • F)=c • cubicThetaSectionFunction F := rfl
  ext i
  simp only [cubicThetaSectionGradient,cubicThetaSectionDifferential,he,fderiv_const_smul hdF c,
    ContinuousLinearMap.comp_apply,smul_apply]
  exact smul_comm p.val.2 c (cubicThetaSectionDifferential F p (cubicThetaTangentBasis i))

end CubicFirstMoment

end

end OAI
