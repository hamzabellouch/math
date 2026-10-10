import OAI.NumberTheory.CubicMoment.Theta.CubicThetaThetaObservation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueConstant
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFunction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNonzeroSpectralResidue

namespace OAI

/-! Match the actual residue's constant term and frequency lattice with
the normalization of Patterson's theta expansion. This does not identify
the nonzero arithmetic coefficients. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRowFrequency_index (h : Eisenstein) :
    cubicThetaFrequency (-lambdaE*h)=cubicThetaRowFrequency h := by
  have hs : traceLambda^2=(-3:ℂ) := by
    have he := congrArg (fun n : Eisenstein => (n:ℂ)) lambdaE_sq
    push_cast at he
    rw [lambdaE_coe] at he
    convert he using 1
  have h4 : traceLambda^4=(9:ℂ) := by
    calc
      _ = (traceLambda^2)^2 := by ring
      _ = _ := by rw [hs]; norm_num
  unfold cubicThetaFrequency cubicThetaRowFrequency
  push_cast
  rw [lambdaE_coe,h4]
  field_simp [traceLambda_ne_zero]
  linear_combination -(3*(h:ℂ))*hs

def cubicThetaResidueScale : ℂ :=
  (cubicThetaConstant:ℂ)/((Real.pi:ℂ)^2/(54*principalIdealZeta 2))

def cubicThetaNormalizedArithmeticResidue : cubicThetaGlobalEnergySpace :=
  cubicThetaResidueScale • cubicThetaArithmeticResidueEnergy (4/3)

lemma cubicThetaResidueScale_ne_zero : cubicThetaResidueScale≠0 := by
  apply div_ne_zero
  · apply Complex.ofReal_ne_zero.mpr
    unfold cubicThetaConstant
    positivity
  · exact div_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (mul_ne_zero (by norm_num) cubicTheta_principalZeta_two_ne_zero)

lemma cubicThetaResidueScale_constant :
    cubicThetaResidueScale*((3*Real.pi:ℂ)*cubicThetaScatteringResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(cubicThetaConstant:ℂ) := by
  have hr : (Real.sqrt 3:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hz : principalIdealZeta 2≠0 := cubicTheta_principalZeta_two_ne_zero
  have hπ : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hJ : ((9*Real.sqrt 3/2:ℝ):ℂ)*(2*Real.pi/(3*Real.sqrt 3):ℂ)=(3*Real.pi:ℂ) := by
    push_cast
    field_simp
    norm_num
  calc
    _ = cubicThetaResidueScale*(((9*Real.sqrt 3/2:ℝ):ℂ)*
        ((2*Real.pi/(3*Real.sqrt 3):ℂ)*cubicThetaScatteringResidue)) := by rw [← hJ]; ring
    _ = cubicThetaResidueScale*(((9*Real.sqrt 3/2:ℝ):ℂ)*
        ((Real.pi:ℂ)^2/(54*principalIdealZeta 2))) := by
      rw [cubicThetaScatteringResidue,cubicTheta_constant_residue_coefficient]
    _ = _ := by unfold cubicThetaResidueScale; field_simp

theorem cubicThetaNormalizedArithmeticResidue_constant (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ), W v=0) :
    inner ℂ (cubicThetaCuspFourierTest 0 W)
      (cubicThetaCuspRestriction cubicThetaNormalizedArithmeticResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(cubicThetaConstant:ℂ)*cubicThetaZeroRadialTest W (4/3) := by
  rw [cubicThetaNormalizedArithmeticResidue,map_smul,inner_smul_right,
    cubicThetaResidue_zero_observation W hW,← mul_assoc,cubicThetaResidueScale_constant]

end CubicFirstMoment

end

end OAI
