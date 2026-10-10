import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueWhittaker
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScatteringResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaZeroWindow

namespace OAI

/-! Actual weighted Fourier observations of the theta residue. The
arithmetic value of the nonzero Whittaker coefficient remains to be identified. -/
noncomputable section
open Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaObservedWhittakerCoefficient (h : Eisenstein) : ℂ :=
  ((Real.pi:ℂ)/Complex.Gamma (4/3))*cubicThetaArithmeticFourierResidue h (4/3)*
    ((2*(cubicThetaRowHeatScale h)^(1/6:ℝ)/‖cubicThetaRowFrequency h‖:ℝ):ℂ)

theorem cubicThetaResidue_whittaker_observation {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) :
    inner ℂ (cubicThetaCuspFourierTest h W)
      (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3)))=
    cubicThetaObservedWhittakerCoefficient h*
      ∫ v in Set.Ioi (2:ℝ), star (W v)*
        cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v)/(v:ℂ)^3 := by
  have he := cubicThetaResidue_fourier_observation hh W (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at he
  rw [he,cubicThetaPoleRadialTest_whittaker hh W]
  dsimp only [cubicThetaObservedWhittakerCoefficient]
  ring

theorem cubicThetaResidue_zero_observation (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ), W v=0) :
    inner ℂ (cubicThetaCuspFourierTest 0 W)
      (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3)))=
      (3*Real.pi:ℂ)*cubicThetaScatteringResidue*cubicThetaZeroRadialTest W (4/3) := by
  have hc : ContinuousAt (fun s : ℂ => (Real.pi:ℂ)/(s-1)*cubicThetaZeroRadialTest W s) (4/3) :=
    (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (by norm_num)).mul
      ((cubicThetaZeroRadialWindow_entire W hW).continuous.continuousAt (x:=(4/3:ℂ)))
  have ht := (hc.tendsto.mono_left nhdsWithin_le_nhds).mul cubicThetaConstantContinuation_residue
  change Tendsto (fun s : ℂ => ((Real.pi:ℂ)/(s-1)*cubicThetaZeroRadialTest W s)*
      ((s-4/3)*cubicThetaConstantContinuation s)) (𝓝[≠] (4/3:ℂ))
      (𝓝 (((Real.pi:ℂ)/((4/3:ℂ)-1)*cubicThetaZeroRadialTest W (4/3))*
        cubicThetaScatteringResidue)) at ht
  have hp : Tendsto (fun s : ℂ => (s-4/3)*cubicThetaCuspFourierObservable 0 W s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 ((3*Real.pi:ℂ)*cubicThetaScatteringResidue*cubicThetaZeroRadialTest W (4/3))) := by
    have he : ((Real.pi:ℂ)/((4/3:ℂ)-1)*cubicThetaZeroRadialTest W (4/3))*
        cubicThetaScatteringResidue=
        (3*Real.pi:ℂ)*cubicThetaScatteringResidue*cubicThetaZeroRadialTest W (4/3) := by ring
    rw [he] at ht
    apply ht.congr'
    filter_upwards [cubicThetaCuspZeroWindow_continued W hW (s:=(4/3:ℂ)) (by norm_num)] with s hs
    rw [hs]
    ring
  have hr := cubicThetaCuspObservable_residue (cubicThetaCuspFourierTest 0 W)
    (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hr
  exact tendsto_nhds_unique hr hp

end CubicFirstMoment

end

end OAI
