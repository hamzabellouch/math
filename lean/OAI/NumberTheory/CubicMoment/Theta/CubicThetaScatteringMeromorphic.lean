import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMeromorphicIdentity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaZeroRadialMellin

namespace OAI

/-! The explicit scattering coefficient and actual constant observation
agree meromorphically, without assuming nonvanishing of a zeta factor. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

lemma cubicTheta_principalZeta_meromorphic (s : ℂ) : MeromorphicAt principalIdealZeta s := by
  change MeromorphicAt (fun z => principalZetaPrefactor z*
    (principalIdealFEPair.Λ₀ z-(1/z)*principalThetaConstant-
      (1/(1-z))*principalThetaConstant)) s
  exact (principalZetaPrefactor_differentiable.analyticAt s).meromorphicAt.mul
    (((principalIdealFEPair.differentiable_Λ₀.analyticAt s).meromorphicAt.sub
      (((MeromorphicAt.const 1 s).div analyticAt_id.meromorphicAt).mul
        (MeromorphicAt.const principalThetaConstant s))).sub
      (((MeromorphicAt.const 1 s).div (analyticAt_const.sub analyticAt_id).meromorphicAt).mul
        (MeromorphicAt.const principalThetaConstant s)))

lemma cubicThetaRamifiedPower_analytic (b s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (3:ℂ)^(b-3*z)) s := by
  let _ : NeZero (3:ℂ) := ⟨by norm_num⟩
  exact
    ((differentiable_const_cpow_of_neZero (3:ℂ)).analyticAt _).comp
      (f:=fun z : ℂ => b-3*z) (x:=s) (by fun_prop)

lemma cubicThetaZetaAffine_meromorphic (b s : ℂ) :
    MeromorphicAt (fun z : ℂ => principalIdealZeta (3*z-b)) s := by
  have ha : AnalyticAt ℂ (fun z : ℂ => 3*z-b) s := by fun_prop
  exact (cubicTheta_principalZeta_meromorphic (3*s-b)).comp_analyticAt
    (f:=principalIdealZeta) (g:=fun z : ℂ => 3*z-b) ha

theorem cubicThetaConstantContinuation_meromorphic (s : ℂ) :
    MeromorphicAt cubicThetaConstantContinuation s := by
  have hp : MeromorphicAt (fun z : ℂ => 2*(3:ℂ)^(3-3*z)) s :=
    (MeromorphicAt.const 2 s).mul (cubicThetaRamifiedPower_analytic 3 s).meromorphicAt
  have hq : MeromorphicAt (fun z : ℂ => 1-(3:ℂ)^(2-3*z)) s :=
    (analyticAt_const.sub (cubicThetaRamifiedPower_analytic 2 s)).meromorphicAt
  change MeromorphicAt (fun z => (2*(3:ℂ)^(3-3*z)/(1-(3:ℂ)^(2-3*z)))*
    principalIdealZeta (3*z-3)/principalIdealZeta (3*z-2)) s
  exact ((hp.div hq).mul (cubicThetaZetaAffine_meromorphic 3 s)).div
    (cubicThetaZetaAffine_meromorphic 2 s)

theorem cubicThetaCuspZeroObservable_continued {s : ℂ} (hs : 1<s.re) :
    cubicThetaCuspFourierObservable 0 cubicThetaRadialTestWeight =ᶠ[𝓝[≠] s]
      (fun z => ((Real.pi:ℂ)/(z-1))*cubicThetaConstantContinuation z*
        cubicThetaZeroRadialTest cubicThetaRadialTestWeight z) := by
  have hobs : MeromorphicOn (cubicThetaCuspFourierObservable 0 cubicThetaRadialTestWeight)
      {z : ℂ | 1<z.re} :=
    fun z hz => cubicThetaCuspFourierObservable_meromorphic 0 cubicThetaRadialTestWeight hz
  have hrhs : MeromorphicOn (fun z => ((Real.pi:ℂ)/(z-1))*cubicThetaConstantContinuation z*
      cubicThetaZeroRadialTest cubicThetaRadialTestWeight z) {z : ℂ | 1<z.re} := by
    intro z _
    exact (((MeromorphicAt.const (Real.pi:ℂ) z).div
      (analyticAt_id.sub analyticAt_const).meromorphicAt).mul
        (cubicThetaConstantContinuation_meromorphic z)).mul
          (cubicThetaZeroRadialTest_entire.analyticAt z).meromorphicAt
  apply cubicThetaMeromorphic_identity hobs hrhs (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by norm_num) hs
  have hn : ∀ᶠ z in 𝓝 (4:ℂ), 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  exact cubicThetaCuspZeroObservable_normalized cubicThetaRadialTestWeight hz

end CubicFirstMoment

end

end OAI
