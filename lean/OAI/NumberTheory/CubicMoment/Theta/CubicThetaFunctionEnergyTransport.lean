import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCutoffEnergy

namespace OAI

/-! Exact transformation and vertical formulas for the hyperbolic
energy of scalar coordinate functions. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaFunctionEnergy_mobius (f : ℂ × ℝ → ℂ) (g : SL(2,ℂ))
    {p : ℂ × ℝ} (hp : 0<p.2) (hf : DifferentiableAt ℝ f (cubicThetaMobius g p)) :
    p.2^2*cubicThetaFunctionEnergy (fun q => f (cubicThetaMobius g q)) p=
      (cubicThetaMobius g p).2^2*cubicThetaFunctionEnergy f (cubicThetaMobius g p) := by
  have hM := (cubicThetaMobius_contDiffAt g hp).differentiableAt (by simp)
  have hcomp := fderiv_comp p hf hM
  simp only [Function.comp_def] at hcomp
  have he : (fderiv ℝ (fun q => f (cubicThetaMobius g q)) p).comp
      cubicThetaTangentCoordinates.toContinuousLinearMap=
      ((fderiv ℝ f (cubicThetaMobius g p)).comp cubicThetaTangentCoordinates.toContinuousLinearMap).comp
        (cubicThetaTangentDerivative g p) := by
    rw [hcomp]
    ext u
    simp only [cubicThetaTangentDerivative,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply]
  unfold cubicThetaFunctionEnergy
  rw [he,cubicThetaTangentEnergy_derivative _ g hp]
  field_simp [hp.ne']

lemma cubicThetaFunctionEnergy_vertical {f : ℝ → ℂ} {p : ℂ × ℝ}
    (hf : DifferentiableAt ℝ f p.2) :
    cubicThetaFunctionEnergy (fun q => f q.2) p=‖deriv f p.2‖^2 := by
  have hs : DifferentiableAt ℝ (fun q : ℂ × ℝ => q.2) p := differentiableAt_snd
  have he := fderiv_comp p hf hs
  simp only [Function.comp_def] at he
  have hd := hf.hasDerivAt.hasFDerivAt.fderiv
  have hds := (hasFDerivAt_snd (𝕜:=ℝ) (E:=ℂ) (F:=ℝ) (p:=p)).fderiv
  unfold cubicThetaFunctionEnergy
  rw [cubicThetaTangentEnergy_coordinates,he,hd,hds]
  simp

end CubicFirstMoment

end

end OAI
