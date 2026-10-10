import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEnergyInverseContinuation

namespace OAI

/-! Transport from the actual energy space to the actual quotient L2
space. Both inverse identities are retained, including at real regular
parameters outside the initial positive-contraction domain. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaEnergyResolventTransport :
    (cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) →L[ℂ]
      (CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2) where
  toFun A := cubicThetaGlobalInclusion.comp (A.comp cubicThetaGlobalInclusion.adjoint)
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro F
    change cubicThetaGlobalInclusion (A (cubicThetaGlobalInclusion.adjoint F)+
      B (cubicThetaGlobalInclusion.adjoint F))=_
    exact cubicThetaGlobalInclusion.map_add _ _
  map_smul' c A := by
    apply ContinuousLinearMap.ext
    intro F
    change cubicThetaGlobalInclusion (c • A (cubicThetaGlobalInclusion.adjoint F))=
      c • cubicThetaGlobalInclusion (A (cubicThetaGlobalInclusion.adjoint F))
    exact cubicThetaGlobalInclusion.map_smul c _
  cont := (continuous_id.clm_comp_const cubicThetaGlobalInclusion.adjoint).const_clm_comp
    cubicThetaGlobalInclusion

def cubicThetaEnergyValueResolvent (z : ℂ) : CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2 :=
  cubicThetaEnergyResolventTransport (Ring.inverse (cubicThetaEnergyPencil z))

lemma cubicThetaEnergyValueResolvent_left {z : ℂ}
    (hu : IsUnit (cubicThetaEnergyPencil z)) :
    (1-z • cubicThetaGlobalGreen)*cubicThetaEnergyValueResolvent z=cubicThetaGlobalGreen := by
  apply ContinuousLinearMap.ext
  intro F
  have h := congrArg
    (fun A : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace =>
      cubicThetaGlobalInclusion (A (cubicThetaGlobalInclusion.adjoint F)))
    (Ring.mul_inverse_cancel (cubicThetaEnergyPencil z) hu)
  change cubicThetaGlobalInclusion
    (Ring.inverse (cubicThetaEnergyPencil z) (cubicThetaGlobalInclusion.adjoint F)-
      z • cubicThetaGlobalInclusion.adjoint (cubicThetaGlobalInclusion
        (Ring.inverse (cubicThetaEnergyPencil z) (cubicThetaGlobalInclusion.adjoint F))))=
      cubicThetaGlobalInclusion (cubicThetaGlobalInclusion.adjoint F) at h
  change cubicThetaGlobalInclusion
    (Ring.inverse (cubicThetaEnergyPencil z) (cubicThetaGlobalInclusion.adjoint F))-
      z • cubicThetaGlobalInclusion (cubicThetaGlobalInclusion.adjoint (cubicThetaGlobalInclusion
        (Ring.inverse (cubicThetaEnergyPencil z) (cubicThetaGlobalInclusion.adjoint F))))=
    cubicThetaGlobalInclusion (cubicThetaGlobalInclusion.adjoint F)
  simpa only [map_sub,map_smul] using h

lemma cubicThetaEnergyValueResolvent_right {z : ℂ}
    (hu : IsUnit (cubicThetaEnergyPencil z)) :
    cubicThetaEnergyValueResolvent z*(1-z • cubicThetaGlobalGreen)=cubicThetaGlobalGreen := by
  apply ContinuousLinearMap.ext
  intro F
  have h := congrArg
    (fun A : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace =>
      cubicThetaGlobalInclusion (A (cubicThetaGlobalInclusion.adjoint F)))
    (Ring.inverse_mul_cancel (cubicThetaEnergyPencil z) hu)
  change cubicThetaGlobalInclusion (Ring.inverse (cubicThetaEnergyPencil z)
    (cubicThetaGlobalInclusion.adjoint F-z • cubicThetaGlobalInclusion.adjoint
      (cubicThetaGlobalInclusion (cubicThetaGlobalInclusion.adjoint F))))=
    cubicThetaGlobalInclusion (cubicThetaGlobalInclusion.adjoint F) at h
  change cubicThetaGlobalInclusion (Ring.inverse (cubicThetaEnergyPencil z)
    (cubicThetaGlobalInclusion.adjoint
      (F-z • cubicThetaGlobalInclusion (cubicThetaGlobalInclusion.adjoint F))))=
    cubicThetaGlobalInclusion (cubicThetaGlobalInclusion.adjoint F)
  simpa only [map_sub,map_smul] using h

lemma cubicThetaGlobalGreen_unit_of_energy {z : ℂ}
    (hu : IsUnit (cubicThetaEnergyPencil z)) : IsUnit (1-z • cubicThetaGlobalGreen) := by
  let Q := 1-z • cubicThetaGlobalGreen
  let C := 1+z • cubicThetaEnergyValueResolvent z
  have hQC : Q*C=1 := by
    dsimp only [C]
    rw [mul_add,mul_one,mul_smul_comm,cubicThetaEnergyValueResolvent_left hu]
    dsimp only [Q]
    abel
  have hCQ : C*Q=1 := by
    dsimp only [C]
    rw [add_mul,one_mul,smul_mul_assoc,cubicThetaEnergyValueResolvent_right hu]
    dsimp only [Q]
    abel
  exact ⟨⟨Q,C,hQC,hCQ⟩,rfl⟩

lemma cubicThetaEnergyValueResolvent_eq {z : ℂ}
    (hu : IsUnit (cubicThetaEnergyPencil z)) :
    cubicThetaEnergyValueResolvent z=cubicThetaGlobalResolvent z := by
  have h := cubicThetaEnergyValueResolvent_left hu
  have hQ := cubicThetaGlobalGreen_unit_of_energy hu
  unfold cubicThetaGlobalResolvent
  calc
    _ = Ring.inverse (1-z • cubicThetaGlobalGreen)*
        ((1-z • cubicThetaGlobalGreen)*cubicThetaEnergyValueResolvent z) := by
      rw [← mul_assoc,Ring.inverse_mul_cancel _ hQ,one_mul]
    _ = _ := congrArg (fun A => Ring.inverse (1-z • cubicThetaGlobalGreen)*A) h

end CubicFirstMoment

end

end OAI
