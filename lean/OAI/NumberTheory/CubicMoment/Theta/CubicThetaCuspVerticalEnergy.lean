import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspLogSection
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCutoffEnergy

namespace OAI

/-! The radial derivative in a cusp is controlled by the actual
hyperbolic Dirichlet energy of the pulled-back cubic section. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaTangentEnergy_apply (L : CubicThetaTangent →L[ℝ] ℂ) (u : CubicThetaTangent) :
    ‖L u‖^2≤cubicThetaTangentEnergy L*‖u‖^2 := by
  have he : cubicThetaTangentEnergy L=
      ‖Complex.reCLM.comp L‖^2+‖Complex.imCLM.comp L‖^2 :=
    cubicThetaTangentEnergy_basis cubicThetaTangentBasis L
  have hr := (Complex.reCLM.comp L).le_opNorm u
  have hi := (Complex.imCLM.comp L).le_opNorm u
  have hr2 := (sq_le_sq₀ (_root_.norm_nonneg ((Complex.reCLM.comp L) u))
    (mul_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg u))).mpr hr
  have hi2 := (sq_le_sq₀ (_root_.norm_nonneg ((Complex.imCLM.comp L) u))
    (mul_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg u))).mpr hi
  rw [he,← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  simp only [ContinuousLinearMap.comp_apply,Complex.reCLM_apply,Complex.imCLM_apply,
    Real.norm_eq_abs,sq_abs,mul_pow] at hr2 hi2
  nlinarith

def cubicThetaVerticalTangent : CubicThetaTangent := cubicThetaTangentCoordinates.symm (0,1)

lemma cubicThetaVerticalTangent_norm : ‖cubicThetaVerticalTangent‖=1 := by
  have h := cubicThetaTangent_norm_sq cubicThetaVerticalTangent
  simp only [cubicThetaVerticalTangent,ContinuousLinearEquiv.apply_symm_apply,
    cubicThetaRadius,Complex.normSq_zero,one_pow,zero_add] at h
  change ‖cubicThetaVerticalTangent‖^2=1 at h
  nlinarith [_root_.norm_nonneg cubicThetaVerticalTangent]

def cubicThetaVerticalPoint (z : ℂ) (v : ℝ) (hv : 0<v) : CubicThetaPoint := ⟨(z,v),hv⟩

lemma cubicThetaCuspSection_deriv (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : 0<v) :
    deriv (fun t : ℝ => cubicThetaSectionFunction F
      (cubicThetaMobius (cubicThetaFullComplex δ) (z,t))) v=
      ((cubicThetaSectionDifferential F (δ • cubicThetaVerticalPoint z v hv)).comp
        (cubicThetaTangentDerivative (cubicThetaFullComplex δ) (z,v))) cubicThetaVerticalTangent := by
  have hm := (cubicThetaMobius_contDiffAt (cubicThetaFullComplex δ) (p:=(z,v)) hv).differentiableAt
    (by simp)
  have hp := cubicThetaMobius_height_pos (cubicThetaFullComplex δ) (p:=(z,v)) hv
  have hf := cubicThetaSectionFunction_differentiable F hp
  have hline : HasDerivAt (fun t : ℝ => (z,t)) (0,1) v :=
    (hasDerivAt_const v z).prodMk (hasDerivAt_id v)
  have h := (hf.hasFDerivAt.comp_hasDerivAt v (hm.hasFDerivAt.comp_hasDerivAt v hline)).deriv
  have hpoint : (δ • cubicThetaVerticalPoint z v hv).val=
      cubicThetaMobius (cubicThetaFullComplex δ) (z,v) := rfl
  simpa only [cubicThetaSectionDifferential,cubicThetaTangentDerivative,cubicThetaVerticalTangent,
    ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply,hpoint,Function.comp_def] using h

theorem cubicThetaCuspSection_vertical_energy (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : 0<v) :
    v^2*‖deriv (fun t : ℝ => cubicThetaSectionFunction F
      (cubicThetaMobius (cubicThetaFullComplex δ) (z,t))) v‖^2≤
      cubicThetaSectionEnergy F (δ • cubicThetaVerticalPoint z v hv) := by
  rw [cubicThetaCuspSection_deriv δ F z hv]
  have h := cubicThetaTangentEnergy_apply
    ((cubicThetaSectionDifferential F (δ • cubicThetaVerticalPoint z v hv)).comp
      (cubicThetaTangentDerivative (cubicThetaFullComplex δ) (z,v))) cubicThetaVerticalTangent
  rw [cubicThetaVerticalTangent_norm,one_pow,mul_one,
    cubicThetaTangentEnergy_derivative _ _ hv] at h
  have hb := mul_le_mul_of_nonneg_left h (sq_nonneg v)
  apply hb.trans_eq
  change v^2*(((cubicThetaMobius (cubicThetaFullComplex δ) (z,v)).2/v)^2*
    cubicThetaTangentEnergy (cubicThetaSectionDifferential F (δ • cubicThetaVerticalPoint z v hv)))=
    (cubicThetaMobius (cubicThetaFullComplex δ) (z,v)).2^2*
      cubicThetaTangentEnergy (cubicThetaSectionDifferential F (δ • cubicThetaVerticalPoint z v hv))
  field_simp [hv.ne']

end CubicFirstMoment

end

end OAI
