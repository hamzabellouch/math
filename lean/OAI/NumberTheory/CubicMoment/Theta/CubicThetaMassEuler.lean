import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSquarefreeMassEuler

namespace OAI

/-! An explicit zeta expression for the squared arithmetic theta coefficients. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaMassEulerPrefactor (s : ℂ) : ℂ :=
  (6*3^(8:ℂ)*((1-(3:ℂ)^(-2-3*s))⁻¹-1) +
    2*(3:ℂ)^(8-s)*(1-(3:ℂ)^(-2-3*s))⁻¹) *
  (1-(3:ℂ)^(-(1+s))) * (1-(3:ℂ)^(-(2+3*s))) /
  (1-(3:ℂ)^(-(2+2*s)))

lemma cubicThetaThree_rpow_complex (t : ℝ) :
    (((3:ℝ)^t:ℝ):ℂ)=(3:ℂ)^(t:ℂ) :=
  Complex.ofReal_cpow (by norm_num) t

theorem cubicThetaCoefficientMass_euler {σ : ℝ} (hσ : 0 < σ) :
    (cubicThetaCoefficientMass σ:ℂ)=cubicThetaMassEulerPrefactor (σ:ℂ)*
      principalIdealZeta (1+(σ:ℂ))*principalIdealZeta (2+3*(σ:ℂ))/
      principalIdealZeta (2+2*(σ:ℂ)) := by
  rw [cubicThetaCoefficientMass_primary_quotient hσ]
  simp only [Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_inv,
    Complex.ofReal_div,cubicThetaRamifiedRatio,cubicThetaThree_rpow_complex,
    Complex.ofReal_ofNat,Complex.ofReal_one]
  rw [cubicThetaPrimaryMass_euler (by linarith : 1 < 1+σ),
    cubicThetaPrimaryMass_euler (by linarith : 1 < 2+2*σ),
    cubicThetaPrimaryMass_euler (by linarith : 1 < 2+3*σ)]
  push_cast
  unfold cubicThetaMassEulerPrefactor
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma cubicThetaMassEulerPrefactor_zero : cubicThetaMassEulerPrefactor 0=2*3^(8:ℂ) := by
  norm_num [cubicThetaMassEulerPrefactor,Complex.cpow_neg,Complex.cpow_ofNat]

end CubicFirstMoment

end

end OAI
