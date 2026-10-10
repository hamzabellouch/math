import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEnergyMellin
import OAI.NumberTheory.CubicMoment.Estimates.CubicWhittakerEnergyContinuity

namespace OAI

/-! The Mellin pole of the actual nonconstant horizontal energy, retaining
the squared Whittaker mass that will enter the geometric norm comparison. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CubicFirstMoment

theorem cubicThetaArithmeticFourierEnergy_residue :
    Tendsto (fun σ : ℝ => (σ:ℂ)*
      ((∫ v in Ioi (0:ℝ), v^(2*σ-1)*cubicThetaArithmeticFourierEnergy v:ℝ):ℂ))
      (𝓝[>] 0) (𝓝 ((cubicWhittakerEnergyMass 0:ℂ)*
        ((2*3^(8:ℂ))*(principalThetaConstant/(residueHeckeScale 1:ℂ))))) := by
  have hp : Tendsto (fun σ : ℝ => (81:ℝ)^σ) (𝓝[>] 0) (𝓝 1) := by
    have h := (Real.continuousAt_const_rpow (by norm_num : (81:ℝ)≠0) (b:=0)).tendsto
    simpa only [Real.rpow_zero] using h.mono_left nhdsWithin_le_nhds
  have he : Tendsto (fun σ : ℝ => ((81^σ*cubicWhittakerEnergyMass σ:ℝ):ℂ))
      (𝓝[>] 0) (𝓝 (cubicWhittakerEnergyMass 0:ℂ)) := by
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (hp.mul cubicWhittakerEnergyMass_tendsto_zero)
    simpa only [one_mul,Function.comp_def] using h
  apply (he.mul cubicThetaCoefficientMass_residue).congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [cubicThetaArithmeticFourierEnergy_mellin hσ,Complex.ofReal_mul,Complex.ofReal_mul]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
