import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalGreen

namespace OAI

/-! The global resolvent has a genuine energy lift solving the weak
mass-plus-gradient equation. This does not assume elliptic regularity. -/
noncomputable section
open scoped InnerProduct
namespace CubicFirstMoment

lemma cubicThetaGlobalEnergy_inner (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ u v=inner ℂ (cubicThetaGlobalInclusion u) (cubicThetaGlobalInclusion v)+
      inner ℂ (cubicThetaGlobalEnergyGradient u) (cubicThetaGlobalEnergyGradient v) :=
  WithLp.prod_inner_apply (u:CubicThetaGlobalEnergyAmbient) (v:CubicThetaGlobalEnergyAmbient)

def cubicThetaGlobalResolventLift (z : ℂ) (F : CubicThetaGlobalL2) : cubicThetaGlobalEnergySpace :=
  cubicThetaGlobalWeakSolution (F+z • cubicThetaGlobalResolvent z F)

lemma cubicThetaGlobalResolventLift_value {z : ℂ} (hz : z.im≠0 ∨ z.re<1)
    (F : CubicThetaGlobalL2) :
    cubicThetaGlobalInclusion (cubicThetaGlobalResolventLift z F)=cubicThetaGlobalResolvent z F := by
  rw [cubicThetaGlobalResolventLift,← cubicThetaGlobalGreen_apply,
    ← cubicThetaGlobalResolvent_range hz]

theorem cubicThetaGlobalResolventLift_weak {z : ℂ} (hz : z.im≠0 ∨ z.re<1)
    (F : CubicThetaGlobalL2) (v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalEnergyGradient v)
        (cubicThetaGlobalEnergyGradient (cubicThetaGlobalResolventLift z F))+
      (1-z)*inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaGlobalResolvent z F)=
      inner ℂ (cubicThetaGlobalInclusion v) F := by
  have he : inner ℂ v (cubicThetaGlobalResolventLift z F)=
      inner ℂ (cubicThetaGlobalInclusion v) (F+z • cubicThetaGlobalResolvent z F) := by
    rw [cubicThetaGlobalResolventLift,cubicThetaGlobalWeakSolution_eq_adjoint]
    exact cubicThetaGlobalInclusion.adjoint_inner_right _ _

  rw [cubicThetaGlobalEnergy_inner,cubicThetaGlobalResolventLift_value hz,
    inner_add_right,inner_smul_right] at he
  linear_combination he

end CubicFirstMoment

end

end OAI
