import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFrequencyRemovable

namespace OAI

/-! The endpoint s=2 is included: the actual residue and its arithmetic
Fourier observations are removable there as well. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

theorem cubicThetaForcedEnergy_removable_closed {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2)
    (hne : (σ:ℂ)≠4/3) :
    ∃ g : ℂ → cubicThetaGlobalEnergySpace, AnalyticAt ℂ g (σ:ℂ) ∧
      (fun s => cubicThetaContinuedEnergyLift (cubicThetaGlobalSpectralParameter s)
        (cubicThetaForcingL2 s))=ᶠ[𝓝[≠] (σ:ℂ)] g := by
  apply cubicThetaSimpleResidue_removable (cubicThetaForcedEnergy_meromorphic (by simpa using hσ))
  have ht := cubicThetaForcedEnergy_residue_closed hσ hσ2
  rwa [cubicThetaArithmeticResidueEnergy_vanishes_closed hσ hσ2 hne] at ht

theorem cubicThetaForcedResolvent_removable_closed {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2)
    (hne : (σ:ℂ)≠4/3) :
    ∃ g : ℂ → CubicThetaGlobalL2, AnalyticAt ℂ g (σ:ℂ) ∧
      cubicThetaForcedResolvent=ᶠ[𝓝[≠] (σ:ℂ)] g := by
  apply cubicThetaSimpleResidue_removable (cubicThetaForcedResolvent_meromorphic (by simpa using hσ))
  have ht := cubicThetaForcedResolvent_residue_closed hσ hσ2
  simpa only [cubicThetaArithmeticResidueEnergy_vanishes_closed hσ hσ2 hne,map_zero] using ht

theorem cubicThetaFrequencyContinuation_removable_closed {h : Eisenstein} (hh : h≠0)
    {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) (hne : (σ:ℂ)≠4/3) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (σ:ℂ) ∧
      cubicThetaFrequencyContinuation h=ᶠ[𝓝[≠] (σ:ℂ)] g := by
  obtain ⟨g,hg,he⟩ := cubicThetaForcedEnergy_removable_closed hσ hσ2 hne
  let L : cubicThetaGlobalEnergySpace →L[ℂ] ℂ :=
    (innerSL ℂ (cubicThetaCuspFourierTest h cubicThetaRadialTestWeight)).comp cubicThetaCuspRestriction
  let R := cubicThetaFourierRadialTest h cubicThetaRadialTestWeight
  have hR : AnalyticAt ℂ R (σ:ℂ) :=
    (cubicThetaFourierRadialTest_entire hh cubicThetaRadialTestWeight).analyticAt _
  have hRn : R (σ:ℂ)≠0 := by
    intro hz
    change cubicThetaFourierRadialTest h cubicThetaRadialTestWeight (σ:ℂ)=0 at hz
    have hp := cubicThetaFourierRadialTest_real_pos hh σ
    rw [hz,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  have hπ : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  have hG := cubicThetaGamma_analytic_right (s:=(σ:ℂ)) (by simp; linarith)
  have hL : AnalyticAt ℂ (fun s => L (g s)) (σ:ℂ) :=
    (L.analyticAt (g σ)).comp (f:=g) (x:=(σ:ℂ)) hg
  refine ⟨fun s => Complex.Gamma s/((Real.pi:ℂ)*R s)*L (g s),
    (hG.div (analyticAt_const.mul hR) (mul_ne_zero hπ hRn)).mul hL,?_⟩
  have hn : ∀ᶠ s in 𝓝 (σ:ℂ), s.re<3 :=
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by simp; linarith)
  filter_upwards [nhdsWithin_le_nhds hn,he] with s hs hes
  simp only [cubicThetaFrequencyContinuation,ite_eq_right (not_lt.mpr hs.le),
    cubicThetaFrequencyQuotient,cubicThetaCuspFourierObservable,cubicThetaCuspObservable,
    cubicThetaForcedCusp]
  rw [hes]
  change Complex.Gamma s * L (g s) / ((Real.pi:ℂ)*R s)=_
  ring

end CubicFirstMoment

end

end OAI
