import OAI.NumberTheory.CubicMoment.Theta.CubicThetaBaseScalarSign
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaVerticalSeriesDerivative

namespace OAI

/-! Inversion fixes the axis derivative at height one. A negative real
arithmetic derivative determines the remaining sign of the base scalar. -/
noncomputable section
open Filter Set
open scoped Topology
namespace CubicFirstMoment

def cubicThetaArithmeticAxisDerivative (v : ℝ) : ℂ :=
  ∑' n : Eisenstein,cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 v n

lemma cubicThetaArithmeticAxis_hasDerivAt {v : ℝ} (hv : 0<v) :
    HasDerivAt cubicThetaArithmeticAxis (cubicThetaArithmeticAxisDerivative v) v := by
  have h := cubicThetaAngular_vertical_hasDerivAt (by norm_num : (0:ℝ)≤81)
    cubicThetaArithmeticCoefficient_bound 0 hv 0
  have he : cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient 0=cubicThetaArithmeticCoefficient := by
    funext n
    simp only [cubicThetaAngularCoefficient,Int.natAbs_zero,pow_zero,theta_zero,one_mul]
  rw [he] at h
  exact h


lemma cubicThetaArithmeticAxisDerivative_balance :
    cubicThetaArithmeticAxisDerivative 1= -(2/3:ℂ)*cubicThetaSeriesConstant := by
  let A := cubicThetaArithmeticAxisDerivative 1
  have hA : HasDerivAt cubicThetaArithmeticAxis A 1 :=
    cubicThetaArithmeticAxis_hasDerivAt (by norm_num)
  have hinv : HasDerivAt (fun v : ℝ => v⁻¹) (-1) 1 := by
    simpa using (hasDerivAt_inv (by norm_num : (1:ℝ)≠0))
  have hAi : HasDerivAt (fun v : ℝ => cubicThetaArithmeticAxis v⁻¹) (-A) 1 := by
    have hA' : HasDerivAt cubicThetaArithmeticAxis A ((1:ℝ)⁻¹) := by simpa using hA
    simpa only [Function.comp_def,Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] using
      hA'.scomp 1 hinv
  have hp : HasDerivAt (fun v : ℝ => ((v^(2/3:ℝ):ℝ):ℂ)) (2/3) 1 := by
    convert (Real.hasDerivAt_rpow_const (x:=1) (p:=(2/3:ℝ)) (Or.inl (by norm_num))).ofReal_comp using 1; norm_num
  have hpi : HasDerivAt (fun v : ℝ => (((v⁻¹)^(2/3:ℝ):ℝ):ℂ)) (-(2/3)) 1 := by
    have hp' : HasDerivAt (fun v : ℝ => ((v^(2/3:ℝ):ℝ):ℂ)) (2/3) ((1:ℝ)⁻¹) := by simpa using hp
    simpa only [Function.comp_def,Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] using
      hp'.scomp 1 hinv
  have hR := hAi.add ((hpi.sub hp).const_mul cubicThetaSeriesConstant)
  have he : cubicThetaArithmeticAxis =ᶠ[𝓝 (1:ℝ)]
      (fun v => cubicThetaArithmeticAxis v⁻¹+cubicThetaSeriesConstant*
        ((((v⁻¹)^(2/3:ℝ):ℝ):ℂ)-((v^(2/3:ℝ):ℝ):ℂ))) := by
    filter_upwards [show Ioi (0:ℝ)∈𝓝 1 from Ioi_mem_nhds (by norm_num)] with v hv
    exact cubicThetaArithmetic_center_small hv
  have h := hA.unique (hR.congr_of_eventuallyEq he)
  change A= -A+cubicThetaSeriesConstant*(-(2/3)-(2/3)) at h
  dsimp [A] at h
  linear_combination (1/2:ℂ)*h

theorem cubicThetaArithmeticBaseScalar_eq_one_of_axisDerivative_neg
    (hneg : (cubicThetaArithmeticAxisDerivative 1).re<0) :
    cubicThetaArithmeticBaseScalar=1 := by
  rcases cubicThetaArithmeticBaseScalar_sign with h | h
  · exact h
  · rw [cubicThetaArithmeticAxisDerivative_balance,cubicThetaSeriesConstant,h] at hneg
    have hC : 0<cubicThetaConstant := by unfold cubicThetaConstant; positivity
    norm_num [div_neg] at hneg
    nlinarith

end CubicFirstMoment

end

end OAI
