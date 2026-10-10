import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEnergyRegularDomain

namespace OAI

/-! The exact residue of the actual energy inverse. The complementary
inverse is analytic and the exceptional projection gives a simple pole. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

lemma cubicThetaProjectedInverse_analytic {z : ℝ} (hz : 0≤z) (hz2 : z<2) :
    AnalyticAt ℂ (fun w : ℂ => Ring.inverse
      (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection (z:ℂ))) (z:ℂ) := by
  have hu := cubicThetaProjectedPencil_unit hz hz2
  have hi : AnalyticAt ℂ Ring.inverse
      (cubicThetaEnergyPencil (z:ℂ)+cubicThetaExceptionalProjection (z:ℂ)) := by
    convert analyticAt_inverse (𝕜:=ℂ)
      (A:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) hu.unit using 1
    exact hu.unit_spec
  exact hi.comp (f:=fun w : ℂ => cubicThetaEnergyPencil w+cubicThetaExceptionalProjection (z:ℂ))
    (x:=(z:ℂ)) ((cubicThetaEnergyPencil_analytic (z:ℂ)).add analyticAt_const)

private lemma scale_pole {E : Type*} [AddCommGroup E] [Module ℂ E]
    {z w : ℂ} (hw : w≠z) (u v : E) :
    (w-z) • (u+(z/(z-w)) • v)=(w-z) • u+(-z) • v := by
  have hc : (w-z)*(z/(z-w))=-z := by
    field_simp [sub_ne_zero.mpr hw.symm]
    ring
  rw [smul_add,smul_smul,hc]

lemma cubicThetaLocalEnergyResolvent_scaled {z w : ℂ} (hw : w≠z) :
    (w-z) • cubicThetaLocalEnergyResolvent z w=
      (w-z) • (Ring.inverse (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection z)*
        (1-cubicThetaExceptionalProjection z))+(-z) • cubicThetaExceptionalProjection z := by
  apply ContinuousLinearMap.ext
  intro u
  change (w-z) • ((Ring.inverse (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection z)*
    (1-cubicThetaExceptionalProjection z)) u+(z/(z-w)) • cubicThetaExceptionalProjection z u)=
    (w-z) • ((Ring.inverse (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection z)*
    (1-cubicThetaExceptionalProjection z)) u)+(-z) • cubicThetaExceptionalProjection z u
  exact scale_pole hw _ _

theorem cubicThetaEnergyInverse_residue {z : ℝ} (hz : 0<z) (hz2 : z<2) :
    Tendsto (fun w : ℂ => (w-(z:ℂ)) • Ring.inverse (cubicThetaEnergyPencil w))
      (𝓝[≠] (z:ℂ)) (𝓝 ((-(z:ℂ)) • cubicThetaExceptionalProjection (z:ℂ))) := by
  let _ : NormedRing (cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) := inferInstance
  let _ : NormedAlgebra ℂ (cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) := inferInstance
  let P : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
    cubicThetaExceptionalProjection (z:ℂ)
  let R : ℂ → (cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) := fun w : ℂ => Ring.inverse (cubicThetaEnergyPencil w+P)*(1-P)
  have hR : ContinuousAt R (z:ℂ) :=
    (cubicThetaProjectedInverse_analytic hz.le hz2).continuousAt.clm_comp continuousAt_const
  have hreg : Tendsto (fun w : ℂ => (w-(z:ℂ)) • R w)
      (𝓝[≠] (z:ℂ)) (𝓝 0) := by
    have ht : Tendsto (fun w : ℂ => w-(z:ℂ)) (𝓝[≠] (z:ℂ)) (𝓝 0) := by
      have hzero : ContinuousAt (fun w : ℂ => w-(z:ℂ)) (z:ℂ) :=
        continuousAt_id.sub continuousAt_const
      simpa only [sub_self] using hzero.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (z:ℂ)≤𝓝 (z:ℂ))
    have h := ht.smul (hR.tendsto.mono_left nhdsWithin_le_nhds)
    simpa only [sub_self,zero_smul] using h
  have hu := cubicThetaProjectedPencil_unit hz.le hz2
  have hevent : ∀ᶠ w : ℂ in 𝓝 (z:ℂ), IsUnit (cubicThetaEnergyPencil w+P) :=
    ((cubicThetaEnergyPencil_analytic (z:ℂ)).add analyticAt_const).continuousAt.eventually
      ((Units.isOpen (R:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace)).mem_nhds hu)
  have he : (fun w : ℂ => (w-(z:ℂ)) • Ring.inverse (cubicThetaEnergyPencil w))=ᶠ[𝓝[≠] (z:ℂ)]
      (fun w => (w-(z:ℂ)) • R w+(-(z:ℂ)) • P) := by
    filter_upwards [nhdsWithin_le_nhds hevent,self_mem_nhdsWithin] with w hw hne
    have hn : w≠(z:ℂ) := hne
    rw [← cubicThetaLocalEnergyResolvent_eq_inverse hz.ne' hn hw]
    exact cubicThetaLocalEnergyResolvent_scaled hn
  have h := hreg.add (tendsto_const_nhds (x:=(-(z:ℂ)) • P))
  simpa only [zero_add] using h.congr' he.symm

end CubicFirstMoment

end

end OAI
