import OAI.NumberTheory.CubicMoment.Theta.CubicThetaExceptionalProjection

namespace OAI

/-! The exceptional projection diagonalizes the energy mass operator.
These exact identities isolate the simple pole in the local inverse. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaExceptionalProjection_idempotent (z : ℂ) :
    cubicThetaExceptionalProjection z*cubicThetaExceptionalProjection z=
      cubicThetaExceptionalProjection z :=
  (cubicThetaEnergyPencil z).ker.isIdempotentElem_starProjection

lemma cubicThetaEnergyMass_mul_projection {z : ℝ} (hz : z≠0) :
    cubicThetaEnergyMass*cubicThetaExceptionalProjection (z:ℂ)=
      ((z⁻¹:ℝ):ℂ) • cubicThetaExceptionalProjection (z:ℂ) := by
  apply ContinuousLinearMap.ext
  intro u
  have hm := (cubicThetaEnergyPencil (z:ℂ)).ker.starProjection_apply_mem u
  change cubicThetaExceptionalProjection (z:ℂ) u-
    (z:ℂ) • (cubicThetaEnergyMass (cubicThetaExceptionalProjection (z:ℂ) u))=0 at hm
  have he := (sub_eq_zero.mp hm).symm
  change cubicThetaEnergyMass (cubicThetaExceptionalProjection (z:ℂ) u)=
    ((z⁻¹:ℝ):ℂ) • (cubicThetaExceptionalProjection (z:ℂ) u)
  conv_rhs => rw [← he,smul_smul,← Complex.ofReal_mul,inv_mul_cancel₀ hz,Complex.ofReal_one,one_smul]

lemma cubicThetaEnergyMass_commute_projection {z : ℝ} (hz : z≠0) :
    Commute cubicThetaEnergyMass (cubicThetaExceptionalProjection (z:ℂ)) := by
  have hA : star cubicThetaEnergyMass=cubicThetaEnergyMass :=
    (ContinuousLinearMap.isPositive_adjoint_comp_self cubicThetaGlobalInclusion).isSelfAdjoint
  have hP : star (cubicThetaExceptionalProjection (z:ℂ))=cubicThetaExceptionalProjection (z:ℂ) :=
    isSelfAdjoint_starProjection _
  have hc : star ((z⁻¹:ℝ):ℂ)=((z⁻¹:ℝ):ℂ) := by rw [RCLike.star_def,Complex.conj_ofReal]
  have he := congrArg star (cubicThetaEnergyMass_mul_projection hz)
  have hm := ContinuousLinearMap.adjoint_comp cubicThetaEnergyMass (cubicThetaExceptionalProjection (z:ℂ))
  change star (cubicThetaEnergyMass*cubicThetaExceptionalProjection (z:ℂ))=
    star (cubicThetaExceptionalProjection (z:ℂ))*star cubicThetaEnergyMass at hm
  have hs := (ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace)
    (F:=cubicThetaGlobalEnergySpace)).map_smulₛₗ ((z⁻¹:ℝ):ℂ) (cubicThetaExceptionalProjection (z:ℂ))
  change star (((z⁻¹:ℝ):ℂ) • cubicThetaExceptionalProjection (z:ℂ))=
    star ((z⁻¹:ℝ):ℂ) • star (cubicThetaExceptionalProjection (z:ℂ)) at hs
  rw [hm,hs,hP,hA,hc] at he
  exact (cubicThetaEnergyMass_mul_projection hz).trans he.symm

lemma cubicThetaEnergyPencil_mul_projection {z : ℝ} (hz : z≠0) (w : ℂ) :
    cubicThetaEnergyPencil w*cubicThetaExceptionalProjection (z:ℂ)=
      (1-w/(z:ℂ)) • cubicThetaExceptionalProjection (z:ℂ) := by
  apply ContinuousLinearMap.ext
  intro u
  have he := congrArg (fun A : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace => A u)
    (cubicThetaEnergyMass_mul_projection hz)
  change cubicThetaEnergyMass (cubicThetaExceptionalProjection (z:ℂ) u)=
    ((z⁻¹:ℝ):ℂ) • (cubicThetaExceptionalProjection (z:ℂ) u) at he
  change cubicThetaExceptionalProjection (z:ℂ) u-w •
      (cubicThetaEnergyMass (cubicThetaExceptionalProjection (z:ℂ) u))=
    (1-w/(z:ℂ)) • (cubicThetaExceptionalProjection (z:ℂ) u)
  rw [he,Complex.ofReal_inv]
  simp only [div_eq_mul_inv]
  module

lemma cubicThetaEnergyPencil_commute_projection {z : ℝ} (hz : z≠0) (w : ℂ) :
    Commute (cubicThetaEnergyPencil w) (cubicThetaExceptionalProjection (z:ℂ)) := by
  apply ContinuousLinearMap.ext
  intro u
  have h := congrArg (fun A : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace => A u)
    (cubicThetaEnergyMass_commute_projection hz).eq
  change cubicThetaEnergyMass (cubicThetaExceptionalProjection (z:ℂ) u)=
    cubicThetaExceptionalProjection (z:ℂ) (cubicThetaEnergyMass u) at h
  change cubicThetaExceptionalProjection (z:ℂ) u-w •
    cubicThetaEnergyMass (cubicThetaExceptionalProjection (z:ℂ) u)=
    cubicThetaExceptionalProjection (z:ℂ) (u-w • cubicThetaEnergyMass u)
  rw [map_sub,map_smul,h]

end CubicFirstMoment

end

end OAI
