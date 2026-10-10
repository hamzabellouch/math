import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEndpointRegularity

namespace OAI

/-! The actual arithmetic family has an analytic germ throughout Re(s)>1,
except for its already proved nonzero pole at 4/3. The representative supplied
by the inverse operator can differ at an isolated singular parameter. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

private lemma analytic_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {A : ℂ → E →L[ℂ] F} {u : ℂ → E} {s : ℂ}
    (hA : AnalyticAt ℂ A s) (hu : AnalyticAt ℂ u s) :
    AnalyticAt ℂ (fun z => A z (u z)) s := by
  have hb := (ContinuousLinearMap.id ℂ (E →L[ℂ] F)).analyticAt_bilinear (A s,u s)
  exact hb.comp (f:=fun z => (A z,u z)) (x:=s) (hA.prod hu)

lemma cubicThetaForcedEnergy_analytic_regular {s : ℂ} (hs : 1<s.re)
    (h : s.im≠0 ∨ 2<s.re) :
    AnalyticAt ℂ (fun z => cubicThetaContinuedEnergyLift
      (cubicThetaGlobalSpectralParameter z) (cubicThetaForcingL2 z)) s := by
  have hp : AnalyticAt ℂ cubicThetaGlobalSpectralParameter s :=
    analyticAt_const.sub (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
  have hA := (cubicThetaEnergyInverse_analytic
    (cubicThetaGlobalSpectralParameter_regular hs h)).comp
      (f:=cubicThetaGlobalSpectralParameter) (x:=s) hp
  have hF := (cubicThetaGlobalInclusion.adjoint.analyticAt (cubicThetaForcingL2 s)).comp
    (f:=cubicThetaForcingL2) (x:=s) (cubicThetaForcingL2_analytic s)
  exact analytic_apply hA hF

lemma cubicThetaForcedResolvent_analytic_regular {s : ℂ} (hs : 1<s.re)
    (h : s.im≠0 ∨ 2<s.re) : AnalyticAt ℂ cubicThetaForcedResolvent s :=
  analytic_apply (cubicThetaGlobalSpectralResolvent_analytic hs h)
    (cubicThetaForcingL2_analytic s)

theorem cubicThetaForcedEnergy_analytic_germ {s : ℂ} (hs : 1<s.re)
    (hne : s≠4/3) :
    ∃ g : ℂ → cubicThetaGlobalEnergySpace, AnalyticAt ℂ g s ∧
      (fun z => cubicThetaContinuedEnergyLift (cubicThetaGlobalSpectralParameter z)
        (cubicThetaForcingL2 z))=ᶠ[𝓝[≠] s] g := by
  by_cases hr : s.im≠0 ∨ 2<s.re
  · exact ⟨_,cubicThetaForcedEnergy_analytic_regular hs hr,Filter.EventuallyEq.rfl⟩
  · have hi : s.im=0 := not_not.mp (not_or.mp hr).1
    have hle : s.re≤2 := le_of_not_gt (not_or.mp hr).2
    have he : (s.re:ℂ)=s := Complex.ext rfl (by simpa using hi.symm)
    simpa only [he] using cubicThetaForcedEnergy_removable_closed hs hle (he.symm ▸ hne)

theorem cubicThetaForcedResolvent_analytic_germ {s : ℂ} (hs : 1<s.re)
    (hne : s≠4/3) :
    ∃ g : ℂ → CubicThetaGlobalL2, AnalyticAt ℂ g s ∧
      cubicThetaForcedResolvent=ᶠ[𝓝[≠] s] g := by
  by_cases hr : s.im≠0 ∨ 2<s.re
  · exact ⟨_,cubicThetaForcedResolvent_analytic_regular hs hr,Filter.EventuallyEq.rfl⟩
  · have hi : s.im=0 := not_not.mp (not_or.mp hr).1
    have hle : s.re≤2 := le_of_not_gt (not_or.mp hr).2
    have he : (s.re:ℂ)=s := Complex.ext rfl (by simpa using hi.symm)
    simpa only [he] using cubicThetaForcedResolvent_removable_closed hs hle (he.symm ▸ hne)

end CubicFirstMoment

end

end OAI
