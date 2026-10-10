import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScatteringRegular

namespace OAI

/-! Away from 4/3, the constant cusp observation of every real spectral
residue vanishes. This alone does not assert vanishing of the full residue. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

theorem cubicThetaSpectralResidue_constant_zero {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2)
    (hne : (σ:ℂ)≠4/3) :
    inner ℂ (cubicThetaCuspFourierTest 0 cubicThetaRadialTestWeight)
      (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy σ))=0 := by
  have hs1 : (σ:ℂ)-1≠0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.sub_re,Complex.ofReal_re,Complex.one_re,Complex.zero_re] at hr
    linarith
  have hc : ContinuousAt (fun s : ℂ => ((Real.pi:ℂ)/(s-1))*cubicThetaConstantContinuation s*
      cubicThetaZeroRadialTest cubicThetaRadialTestWeight s) (σ:ℂ) :=
    ((continuousAt_const.div (continuousAt_id.sub continuousAt_const) hs1).mul
      (cubicThetaConstantContinuation_regular (by simpa using hσ) hne).continuousAt).mul
        (cubicThetaZeroRadialTest_entire.continuous.continuousAt (x:=(σ:ℂ)))
  have hs : Tendsto (fun s : ℂ => s-(σ:ℂ)) (𝓝[≠] (σ:ℂ)) (𝓝 0) := by
    have h : ContinuousAt (fun s : ℂ => s-(σ:ℂ)) (σ:ℂ) :=
      continuousAt_id.sub continuousAt_const
    simpa only [sub_self] using h.tendsto.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun s : ℂ => (s-(σ:ℂ))*cubicThetaCuspFourierObservable 0
      cubicThetaRadialTestWeight s) (𝓝[≠] (σ:ℂ)) (𝓝 0) := by
    have hprod := hs.mul (hc.tendsto.mono_left nhdsWithin_le_nhds)
    simp only [zero_mul] at hprod
    apply hprod.congr'
    filter_upwards [cubicThetaCuspZeroObservable_continued (by simpa using hσ)] with s hs
    rw [hs]
  exact tendsto_nhds_unique
    (cubicThetaCuspObservable_residue (cubicThetaCuspFourierTest 0 cubicThetaRadialTestWeight) hσ hσ2) ht

end CubicFirstMoment

end

end OAI
