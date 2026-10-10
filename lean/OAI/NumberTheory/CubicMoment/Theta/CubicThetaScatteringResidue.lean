import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScatteringMeromorphic

namespace OAI

/-! The constant Fourier observation of the actual spectral residue is
the explicitly computed arithmetic scattering residue. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

def cubicThetaScatteringResidue : ℂ :=
  (principalThetaConstant/(residueHeckeScale 1:ℂ))/(4*principalIdealZeta 2)

theorem cubicThetaCuspZeroObservable_residue :
    Tendsto (fun s : ℂ => (s-4/3)*cubicThetaCuspFourierObservable 0 cubicThetaRadialTestWeight s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (((Real.pi:ℂ)/((4/3:ℂ)-1))*cubicThetaScatteringResidue*
        cubicThetaZeroRadialTest cubicThetaRadialTestWeight (4/3))) := by
  have hp : ContinuousAt (fun s : ℂ => (Real.pi:ℂ)/(s-1)) (4/3:ℂ) :=
    continuousAt_const.div (continuousAt_id.sub continuousAt_const) (by norm_num)
  have hR := cubicThetaZeroRadialTest_entire.continuous.continuousAt (x:=(4/3:ℂ))
  have ht := ((hp.tendsto.mono_left nhdsWithin_le_nhds).mul
    cubicThetaConstantContinuation_residue).mul (hR.tendsto.mono_left nhdsWithin_le_nhds)
  apply ht.congr'
  filter_upwards [cubicThetaCuspZeroObservable_continued (s:=(4/3:ℂ)) (by norm_num)] with s hs
  rw [hs]
  ring

theorem cubicThetaSpectralResidue_constant_observation :
    inner ℂ (cubicThetaCuspFourierTest 0 cubicThetaRadialTestWeight)
        (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3)))=
      ((Real.pi:ℂ)/((4/3:ℂ)-1))*cubicThetaScatteringResidue*
        cubicThetaZeroRadialTest cubicThetaRadialTestWeight (4/3) := by
  apply tendsto_nhds_unique
    (cubicThetaCuspObservable_residue (cubicThetaCuspFourierTest 0 cubicThetaRadialTestWeight)
      (σ:=4/3) (by norm_num) (by norm_num))
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,cubicThetaCuspFourierObservable] using
    cubicThetaCuspZeroObservable_residue

end CubicFirstMoment

end

end OAI
