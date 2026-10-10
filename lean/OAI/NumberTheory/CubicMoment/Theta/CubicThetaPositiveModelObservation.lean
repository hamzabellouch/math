import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticModelObservation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositivePoleScaling
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveZeroWindow

namespace OAI

/-! The explicit nonconstant arithmetic model gives every positive-height
Fourier test of the actual residue, not only its high-cusp restriction. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaPositiveNormalized_nonzero_observation {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW)
      (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicThetaNormalizedObservedCoefficient h*
        cubicThetaFullPoleWeightIntegral h W := by
  have hJ : ((9*Real.sqrt 3/2:ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  rw [cubicThetaNormalizedArithmeticResidue,map_smul,inner_smul_right,
    cubicThetaPositiveResidue_fourier_observation hh W hε hW,
    cubicThetaPositivePoleRadialTest_weight hh W hε hW]
  unfold cubicThetaNormalizedObservedCoefficient cubicThetaObservedWhittakerCoefficient
  field_simp

theorem cubicThetaPositiveModel_nonzero_observation {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW)
      (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)=
      ∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
            cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (z,v) := by
  rw [cubicThetaPositiveNormalized_nonzero_observation hh W hε hW,
    cubicThetaCoefficientScalar hh,cubicThetaFullPoleWeightIntegral,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [cubicThetaArithmeticModel_horizontal _ hv,ite_eq_right hh]
  ring

theorem cubicThetaPositiveNormalized_zero_observation
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 0 W hε hW)
      (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(cubicThetaConstant:ℂ)*
        mellin (star W) (-(4/3:ℂ)) := by
  rw [cubicThetaNormalizedArithmeticResidue,map_smul,inner_smul_right,
    cubicThetaPositiveResidue_zero_observation W hε hW]
  calc
    _ = (cubicThetaResidueScale*((3*Real.pi:ℂ)*cubicThetaScatteringResidue))*
        mellin (star W) (-(4/3:ℂ)) := by ring
    _ = _ := by rw [cubicThetaResidueScale_constant]

theorem cubicThetaPositiveModel_zero_observation
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 0 W hε hW)
      (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)=
      ∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaRowFrequency 0)):ℂ)*
            cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (z,v) := by
  have hm : mellin (star W) (-(4/3:ℂ))=
      ∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*(v:ℂ)^(2/3:ℂ) := by
    rw [show -(4/3:ℂ)=(2/3:ℂ)-2 by ring,
      ←cubicThetaPositiveWindow_power W hε hW (2/3:ℂ)]
    simpa only [div_mul_eq_mul_div] using
      cubicThetaPositiveRadialIntegral_zero_extension W hε.le hW
        (fun v => (v:ℂ)^(2/3:ℂ))
  rw [cubicThetaPositiveNormalized_zero_observation W hε hW,hm,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [cubicThetaArithmeticModel_horizontal _ hv]
  simp only [ite_true,Complex.ofReal_mul]
  have hc : ((v^(2/3:ℝ):ℝ):ℂ)=(v:ℂ)^(2/3:ℂ) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using
      Complex.ofReal_cpow hv.le (2/3:ℝ)
  rw [hc]
  ring

theorem cubicThetaPositiveModel_all_observations
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε)
    (hW : ∀ v≤ε,W v=0) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW)
      (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)=
      ∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
            cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (z,v) := by
  by_cases hh : h=0
  · subst h
    exact cubicThetaPositiveModel_zero_observation W hε hW
  · exact cubicThetaPositiveModel_nonzero_observation hh W hε hW

end CubicFirstMoment

end

end OAI
