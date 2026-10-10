import OAI.NumberTheory.CubicMoment.Theta.CubicThetaForcedResolvent

namespace OAI

/-! Uniqueness for the actual completed energy equation at regular
parameters, used to identify the arithmetic Eisenstein remainder. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaEnergyPencil_inner (z : ℂ) (v u : cubicThetaGlobalEnergySpace) :
    inner ℂ v (cubicThetaEnergyPencil z u)=
      inner ℂ (cubicThetaGlobalEnergyGradient v) (cubicThetaGlobalEnergyGradient u)+
        (1-z)*inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaGlobalInclusion u) := by
  have hsub := inner_sub_right (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace) v u
    (z • cubicThetaGlobalInclusion.adjoint (cubicThetaGlobalInclusion u))
  have hsmul := inner_smul_right (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace) v
    (cubicThetaGlobalInclusion.adjoint (cubicThetaGlobalInclusion u)) z
  have ha := cubicThetaGlobalInclusion.adjoint_inner_right v (cubicThetaGlobalInclusion u)
  change inner ℂ v (cubicThetaGlobalInclusion.adjoint (cubicThetaGlobalInclusion u))=
    inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaGlobalInclusion u) at ha
  have he := cubicThetaGlobalEnergy_inner v u
  change inner ℂ v (u-z • cubicThetaGlobalInclusion.adjoint (cubicThetaGlobalInclusion u))=_
  rw [hsub,hsmul,ha,he]
  ring

theorem cubicThetaContinuedEnergyLift_unique {z : ℂ}
    (hz : IsUnit (cubicThetaEnergyPencil z)) (F : CubicThetaGlobalL2)
    (u : cubicThetaGlobalEnergySpace)
    (hu : ∀ v : cubicThetaGlobalEnergySpace,
      inner ℂ (cubicThetaGlobalEnergyGradient v) (cubicThetaGlobalEnergyGradient u)+
        (1-z)*inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaGlobalInclusion u)=
          inner ℂ (cubicThetaGlobalInclusion v) F) :
    u=cubicThetaContinuedEnergyLift z F := by
  have he : cubicThetaEnergyPencil z u=cubicThetaGlobalInclusion.adjoint F := by
    apply ext_inner_left ℂ
    intro v
    have hf := cubicThetaEnergyPencil_inner z v u
    have ha := cubicThetaGlobalInclusion.adjoint_inner_right v F
    change inner ℂ v (cubicThetaGlobalInclusion.adjoint F)=
      inner ℂ (cubicThetaGlobalInclusion v) F at ha
    exact hf.trans ((hu v).trans ha.symm)
  have h := congrArg (fun w => Ring.inverse (cubicThetaEnergyPencil z) w) he
  have hi := congrArg (fun A : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace => A u)
    (Ring.inverse_mul_cancel (cubicThetaEnergyPencil z) hz)
  exact hi.symm.trans h

end CubicFirstMoment

end

end OAI
