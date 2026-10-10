import OAI.NumberTheory.CubicMoment.Theta.CubicThetaExceptionalProjection
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMeromorphicLinear

namespace OAI

/-! The local candidate inverse at an exceptional real parameter is an
analytic inverse on the complementary subspace plus an explicit simple
pole on the finite exceptional space. Algebraic agreement with the
original inverse is proved separately. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaLocalEnergyResolvent (z w : ℂ) :
    cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
  Ring.inverse (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection z)*
      (1-cubicThetaExceptionalProjection z)+
    (z/(z-w)) • cubicThetaExceptionalProjection z

lemma cubicThetaEnergyPencil_analytic (z : ℂ) : AnalyticAt ℂ cubicThetaEnergyPencil z := by
  let L : ℂ →L[ℂ] (cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight cubicThetaEnergyMass
  have hsm : AnalyticAt ℂ (fun w : ℂ => w • cubicThetaEnergyMass) z := by
    have he : (fun w : ℂ => L w)=(fun w : ℂ => w • cubicThetaEnergyMass) := by
      funext w
      rfl
    rw [← he]
    exact ContinuousLinearMap.analyticAt (𝕜:=ℂ) (E:=ℂ)
      (F:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) L z
  exact analyticAt_const.sub hsm

theorem cubicThetaLocalEnergyResolvent_meromorphic {z : ℝ} (hz : 0≤z) (hz2 : z<2) :
    MeromorphicAt (cubicThetaLocalEnergyResolvent (z:ℂ)) (z:ℂ) := by
  have hu := cubicThetaProjectedPencil_unit hz hz2
  have hi : AnalyticAt ℂ Ring.inverse
      (cubicThetaEnergyPencil (z:ℂ)+cubicThetaExceptionalProjection (z:ℂ)) := by
    convert analyticAt_inverse (𝕜:=ℂ) (A:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) hu.unit using 1
    exact hu.unit_spec
  have hp : AnalyticAt ℂ
      (fun w => cubicThetaEnergyPencil w+cubicThetaExceptionalProjection (z:ℂ)) (z:ℂ) :=
    (cubicThetaEnergyPencil_analytic (z:ℂ)).add analyticAt_const
  have hcomp : AnalyticAt ℂ (fun w : ℂ => Ring.inverse
      (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection (z:ℂ))) (z:ℂ) :=
    hi.comp (f:=fun w : ℂ => cubicThetaEnergyPencil w+cubicThetaExceptionalProjection (z:ℂ)) (x:=(z:ℂ)) hp
  have hmain : AnalyticAt ℂ (fun w : ℂ => Ring.inverse
      (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection (z:ℂ))*
        (1-cubicThetaExceptionalProjection (z:ℂ))) (z:ℂ) := AnalyticAt.mul (𝕜:=ℂ)
    (A:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) hcomp
    (show AnalyticAt ℂ (fun _ : ℂ => 1-cubicThetaExceptionalProjection (z:ℂ)) (z:ℂ)
      from analyticAt_const)
  have hscalar : MeromorphicAt (fun w : ℂ => (z:ℂ)/((z:ℂ)-w)) (z:ℂ) :=
    (MeromorphicAt.const _ _).div ((MeromorphicAt.const _ _).sub (MeromorphicAt.id _))
  exact hmain.meromorphicAt.add (cubicThetaMeromorphic_clm
    ((ContinuousLinearMap.id ℂ ℂ).smulRight (cubicThetaExceptionalProjection (z:ℂ))) hscalar)

end CubicFirstMoment

end

end OAI
