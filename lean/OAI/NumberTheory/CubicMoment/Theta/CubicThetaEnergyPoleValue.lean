import OAI.NumberTheory.CubicMoment.Estimates.CubicWhittakerEnergyValue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEnergyResidue

namespace OAI

/-! Numerical evaluation of the arithmetic horizontal-energy pole. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CubicFirstMoment

lemma cubicWhittakerEnergy_gamma_product :
    Real.Gamma (4/3)*Real.Gamma (2/3)=2*Real.pi/(3*Real.sqrt 3) := by
  have hr := Real.Gamma_mul_Gamma_one_sub (1/3)
  rw [show (1:ℝ)-1/3=2/3 by norm_num,
    show Real.pi*(1/3)=Real.pi/3 by ring,Real.sin_pi_div_three] at hr
  rw [show (4/3:ℝ)=1/3+1 by norm_num,Real.Gamma_add_one (by norm_num : (1/3:ℝ)≠0),
    mul_assoc,hr]
  ring

lemma cubicWhittakerEnergyMass_zero_explicit :
    cubicWhittakerEnergyMass 0=1/(48*Real.pi*Real.sqrt 3) := by
  rw [cubicWhittakerEnergyMass_zero,cubicWhittakerEnergy_gamma_product]
  field_simp
  ring

lemma cubicThetaArithmeticEnergyResidue_value :
    (cubicWhittakerEnergyMass 0:ℂ)*
      ((2*3^(8:ℂ))*(principalThetaConstant/(residueHeckeScale 1:ℂ)))=243/8 := by
  have hr : cubicWhittakerEnergyMass 0 *
      ((2*(3:ℝ)^8)*(Real.pi/(3*Real.sqrt 3)))=243/8 := by
    rw [cubicWhittakerEnergyMass_zero_explicit]
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    field_simp
    nlinarith
  rw [cubicTheta_principalZeta_residue_value]
  norm_num only [Complex.cpow_ofNat]
  norm_num at hr
  have hc := congrArg Complex.ofReal hr
  push_cast at hc
  exact hc

theorem cubicThetaArithmeticFourierEnergy_residue_explicit :
    Tendsto (fun σ : ℝ => (σ:ℂ)*
      ((∫ v in Ioi (0:ℝ), v^(2*σ-1)*cubicThetaArithmeticFourierEnergy v:ℝ):ℂ))
      (𝓝[>] 0) (𝓝 (243/8)) := by
  simpa only [cubicThetaArithmeticEnergyResidue_value] using
    cubicThetaArithmeticFourierEnergy_residue

end CubicFirstMoment

end

end OAI
