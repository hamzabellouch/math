import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalMeromorphic

namespace OAI

/-! At every regular parameter the continued inverse solves the actual
global variational equation. The equation uses the completed gradient
graph and is not an abstract substitute for the geometric Laplacian. -/
noncomputable section
open scoped InnerProduct
namespace CubicFirstMoment

def cubicThetaContinuedEnergyLift (z : ℂ) (F : CubicThetaGlobalL2) :
    cubicThetaGlobalEnergySpace :=
  Ring.inverse (cubicThetaEnergyPencil z) (cubicThetaGlobalInclusion.adjoint F)

lemma cubicThetaContinuedEnergyLift_value {z : ℂ} (hu : IsUnit (cubicThetaEnergyPencil z))
    (F : CubicThetaGlobalL2) :
    cubicThetaGlobalInclusion (cubicThetaContinuedEnergyLift z F)=cubicThetaGlobalResolvent z F := by
  have h := congrArg (fun A : CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2 => A F)
    (cubicThetaEnergyValueResolvent_eq hu)
  exact h

lemma cubicThetaContinuedEnergyLift_equation {z : ℂ} (hu : IsUnit (cubicThetaEnergyPencil z))
    (F : CubicThetaGlobalL2) :
    cubicThetaContinuedEnergyLift z F-z • cubicThetaGlobalInclusion.adjoint
      (cubicThetaGlobalInclusion (cubicThetaContinuedEnergyLift z F))=
        cubicThetaGlobalInclusion.adjoint F := by
  have he := congrArg
    (fun A : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace =>
      A (cubicThetaGlobalInclusion.adjoint F))
    (Ring.mul_inverse_cancel (cubicThetaEnergyPencil z) hu)
  exact he

theorem cubicThetaContinuedEnergyLift_weak {z : ℂ} (hu : IsUnit (cubicThetaEnergyPencil z))
    (F : CubicThetaGlobalL2) (v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalEnergyGradient v)
        (cubicThetaGlobalEnergyGradient (cubicThetaContinuedEnergyLift z F))+
      (1-z)*inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaGlobalResolvent z F)=
      inner ℂ (cubicThetaGlobalInclusion v) F := by
  have hi : inner ℂ v (cubicThetaContinuedEnergyLift z F-z • cubicThetaGlobalInclusion.adjoint
      (cubicThetaGlobalInclusion (cubicThetaContinuedEnergyLift z F)))=
        inner ℂ v (cubicThetaGlobalInclusion.adjoint F) :=
    congrArg (fun u : cubicThetaGlobalEnergySpace => inner ℂ v u)
      (cubicThetaContinuedEnergyLift_equation hu F)
  have hsub := inner_sub_right (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace) v
    (cubicThetaContinuedEnergyLift z F) (z • cubicThetaGlobalInclusion.adjoint
      (cubicThetaGlobalInclusion (cubicThetaContinuedEnergyLift z F)))
  have hsmul := inner_smul_right (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace) v
    (cubicThetaGlobalInclusion.adjoint
      (cubicThetaGlobalInclusion (cubicThetaContinuedEnergyLift z F))) z
  have ha := cubicThetaGlobalInclusion.adjoint_inner_right v
    (cubicThetaGlobalInclusion (cubicThetaContinuedEnergyLift z F))
  have hb := cubicThetaGlobalInclusion.adjoint_inner_right v F
  change inner ℂ v (cubicThetaGlobalInclusion.adjoint
      (cubicThetaGlobalInclusion (cubicThetaContinuedEnergyLift z F)))=
    inner ℂ (cubicThetaGlobalInclusion v)
      (cubicThetaGlobalInclusion (cubicThetaContinuedEnergyLift z F)) at ha
  change inner ℂ v (cubicThetaGlobalInclusion.adjoint F)=
    inner ℂ (cubicThetaGlobalInclusion v) F at hb
  have hform := hsub.trans (congrArg
    (fun w : ℂ => inner ℂ v (cubicThetaContinuedEnergyLift z F)-w) hsmul)
  have hnorm := hform.trans (congrArg
    (fun w : ℂ => inner ℂ v (cubicThetaContinuedEnergyLift z F)-z*w) ha)
  have hn := hnorm.symm.trans (hi.trans hb)
  have he := cubicThetaGlobalEnergy_inner v (cubicThetaContinuedEnergyLift z F)
  have hfinal := (congrArg (fun w : ℂ => w-z*inner ℂ (cubicThetaGlobalInclusion v)
    (cubicThetaGlobalInclusion (cubicThetaContinuedEnergyLift z F))) he).symm.trans hn
  rw [← cubicThetaContinuedEnergyLift_value hu F]
  linear_combination hfinal

end CubicFirstMoment

end

end OAI
