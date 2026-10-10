import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactPerturbation

namespace OAI

/-! The finite exceptional eigenspace has an actual orthogonal
projection. Adding it to the self-adjoint real pencil removes its kernel. -/
noncomputable section
open scoped InnerProduct
namespace CubicFirstMoment

instance cubicThetaEnergyPencil_ker_complete (z : ℂ) :
    CompleteSpace (cubicThetaEnergyPencil z).ker :=
  (cubicThetaEnergyPencil z).isClosed_ker.isComplete.completeSpace_coe

def cubicThetaExceptionalProjection (z : ℂ) :
    cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
  (cubicThetaEnergyPencil z).ker.starProjection

lemma cubicThetaEnergyPencil_selfAdjoint (z : ℝ) :
    IsSelfAdjoint (cubicThetaEnergyPencil (z:ℂ)) := by
  have hA : IsSelfAdjoint cubicThetaEnergyMass :=
    (ContinuousLinearMap.isPositive_adjoint_comp_self cubicThetaGlobalInclusion).isSelfAdjoint
  have hz : IsSelfAdjoint (z:ℂ) := by
    change star (z:ℂ)=(z:ℂ)
    rw [RCLike.star_def,Complex.conj_ofReal]
  have h1 : IsSelfAdjoint (1 : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) := by
    change ContinuousLinearMap.adjoint (1 : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace)=1
    exact ContinuousLinearMap.adjoint_one
  have hs : IsSelfAdjoint ((z:ℂ) • cubicThetaEnergyMass) :=
    IsSelfAdjoint.smul (R:=ℂ) (A:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) hz hA
  exact IsSelfAdjoint.sub (R:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) h1 hs

lemma cubicThetaExceptionalProjection_compact {z : ℝ} (hz : 0≤z) (hz2 : z<2) :
    IsCompactOperator (cubicThetaExceptionalProjection (z:ℂ)) := by
  have := cubicThetaEnergyPencil_finite_ker hz hz2
  exact (isCompactOperator_of_locallyCompactSpace_rng (cubicThetaEnergyPencil (z:ℂ)).ker.subtypeL).comp_clm
    (cubicThetaEnergyPencil (z:ℂ)).ker.orthogonalProjectionOnto

lemma cubicThetaProjectedPencil_injective (z : ℝ) :
    Function.Injective (cubicThetaEnergyPencil (z:ℂ)+cubicThetaExceptionalProjection (z:ℂ)) := by
  let T := cubicThetaEnergyPencil (z:ℂ)
  let P := cubicThetaExceptionalProjection (z:ℂ)
  have hT : T.toLinearMap.IsSymmetric := (cubicThetaEnergyPencil_selfAdjoint z).isSymmetric
  have hzero (u : cubicThetaGlobalEnergySpace) (hu : (T+P) u=0) : u=0 := by
    have hp : T (P u)=0 := (T.ker.starProjection_apply_mem u)
    have ho : inner ℂ (T u) (P u)=0 := by
      have hs := hT u (P u)
      change inner ℂ (T u) (P u)=inner ℂ u (T (P u)) at hs
      rw [hp,inner_zero_right] at hs
      exact hs
    have hu' : T u+P u=0 := by simpa only [add_apply] using hu
    have he := congrArg (fun v => inner ℂ v (P u)) hu'
    rw [inner_zero_left] at he
    rw [inner_add_left,ho,zero_add] at he
    have hpu : P u=0 := inner_self_eq_zero.mp he
    have htu : T u=0 := by
      rwa [hpu,add_zero] at hu'
    have hself : P u=u := T.ker.starProjection_eq_self_iff.mpr htu
    exact hself.symm.trans hpu
  intro u v huv
  have hsub : (T+P) (u-v)=0 := by rw [map_sub,huv,sub_self]
  exact sub_eq_zero.mp (hzero _ hsub)

theorem cubicThetaProjectedPencil_unit {z : ℝ} (hz : 0≤z) (hz2 : z<2) :
    IsUnit (cubicThetaEnergyPencil (z:ℂ)+cubicThetaExceptionalProjection (z:ℂ)) := by
  obtain ⟨K,hK,hu⟩ := cubicThetaEnergyPencil_compact_regularizer hz hz2
  let P := cubicThetaExceptionalProjection (z:ℂ)
  apply cubicThetaCompactPerturbation_unit _ (K-P)
  · exact hK.sub (cubicThetaExceptionalProjection_compact hz hz2)
  · have he : (cubicThetaEnergyPencil (z:ℂ)+P)+(K-P)=cubicThetaEnergyPencil (z:ℂ)+K := by abel
    rw [he]
    exact hu
  · exact cubicThetaProjectedPencil_injective z

end CubicFirstMoment

end

end OAI
