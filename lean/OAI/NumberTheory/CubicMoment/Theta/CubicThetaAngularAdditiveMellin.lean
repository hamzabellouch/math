import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAdditiveMellin
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularMellin

namespace OAI

/-! The exact shifted Gamma/Dirichlet identity at every horizontal translate. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaAdditiveAngular_series (z : ℂ) (v : ℝ) (ℓ : ℤ) :
    cubicThetaNonconstant (cubicThetaAngularCoefficient (cubicThetaAdditiveCoefficient z) ℓ) (0,v)=
      cubicThetaNonconstant (cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient ℓ) (z,v) := by
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · simp only [cubicThetaSeriesTerm,hn,ite_true]
  · simp only [cubicThetaSeriesTerm,hn,ite_false,cubicThetaAdditiveCoefficient,
      cubicThetaAngularCoefficient,tracePair,mul_zero,Complex.zero_re,
      AddChar.map_zero_eq_one,Circle.coe_one,mul_one]
    ring

theorem cubicThetaAngularAdditive_mellin (z : ℂ) (ℓ : ℤ) {s : ℂ} (hs : 3/2<s.re) :
    mellin (fun v : ℝ => cubicThetaNonconstant
      (cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient ℓ) (z,v))
        (2*s+(ℓ.natAbs:ℂ)-1)=
      (1/4:ℂ)*((2*Real.pi:ℝ):ℂ)^(-2*(s+(ℓ.natAbs:ℂ)/2))*
        Complex.Gamma (s+(ℓ.natAbs:ℂ)/2+1/6)*Complex.Gamma (s+(ℓ.natAbs:ℂ)/2-1/6)*
        cubicThetaDirichlet (fun n => theta ℓ n*cubicThetaAdditiveCoefficient z n) (2*s-1) := by
  simp_rw [←cubicThetaAdditiveAngular_series z]
  exact cubicThetaAngular_completed (by norm_num : (0:ℝ)≤81)
    (cubicThetaAdditiveCoefficient_norm z) ℓ hs

end CubicFirstMoment

end

end OAI
