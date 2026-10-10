import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedAllRows
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimarySeriesRamification

namespace OAI

/-! Cubic inflation with every unit retained, and its exact factor in the
convergent ramified/primary decomposition. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_unit_ramified_cube
    (e : Eisensteinˣ) (n : ℕ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+5)) (lambdaE^3*h)=
      27*cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)) h := by
  by_cases hd : lambdaE^n ∣ h
  · obtain ⟨t,rfl⟩ := hd
    have hp : lambdaE^3*(lambdaE^n*t)=lambdaE^(n+3)*t := by rw [pow_add]; ring
    rw [hp,show n+5=(n+3)+2 by omega,
      cubicThetaEisensteinGaussCoefficient_unit_ramified_inflation,
      cubicThetaEisensteinGaussCoefficient_unit_ramified_inflation]
    have hm : (n+3+2)%3=(n+2)%3 := by omega
    rw [hm,cubicThetaNorm_lambda_pow,cubicThetaNorm_lambda_pow,pow_add]
    push_cast
    ring
  · have hn : ¬lambdaE^(n+3) ∣ lambdaE^3*h := by
      intro hx
      have hp : lambdaE^(n+3)=lambdaE^3*lambdaE^n := by rw [pow_add]; ring
      rw [hp,mul_dvd_mul_iff_left (pow_ne_zero _ lambdaE_prime.ne_zero)] at hx
      exact hd hx
    have hz (k : ℕ) (t : Eisenstein) (hk : ¬lambdaE^k ∣ t) :
        cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(k+2)) t=0 := by
      by_contra he
      apply hk
      simpa only [mul_one] using
        cubicThetaEisensteinGaussCoefficient_full_ramified_support e primary_one k t
          (by simpa only [mul_one] using he)
    rw [show n+5=(n+3)+2 by omega,hz (n+3) _ hn,hz n _ hd,mul_zero]

theorem cubicThetaRamifiedFactor_cube (e : Eisensteinˣ) (n : ℕ) (s : ℂ)
    (h : Eisenstein) :
    cubicThetaRamifiedFactor e (n+3) s (lambdaE^3*h)=
      (27*(27:ℂ)^(-s))*cubicThetaRamifiedFactor e n s h := by
  unfold cubicThetaRamifiedFactor
  rw [show n+3+2=n+5 by omega,
    cubicThetaEisensteinGaussCoefficient_unit_ramified_cube,
    cubicThetaNorm_unit_lambda_pow,cubicThetaNorm_unit_lambda_pow]
  have hp : (3:ℝ)^(n+5)=(27:ℝ)*3^(n+2) := by
    rw [show n+5=3+(n+2) by omega,pow_add]
    norm_num
  rw [hp,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
  push_cast
  ring

theorem cubicThetaPrimaryFourierTerm_cube (e : Eisensteinˣ) (n : ℕ) (s : ℂ)
    (h : Eisenstein) (a : CubicThetaPrimaryPart) :
    cubicThetaPrimaryFourierTerm e (n+3) s (lambdaE^3*h) a=
      cubicThetaPrimaryFourierTerm e n s h a := by
  have hc := cubicSymbol_cube_of_isCoprime a.property lambdaE
    (primary_coprime_lambda a.property)
  unfold cubicThetaPrimaryFourierTerm
  rw [pow_add,hc,mul_one,cubicThetaSymbolFourier_lambda_cube a.property]

theorem cubicThetaRamifiedTerm_cube (e : Eisensteinˣ) (n : ℕ) (s : ℂ)
    (h : Eisenstein) (a : CubicThetaPrimaryPart) :
    cubicThetaRamifiedTerm s (lambdaE^3*h) (e,n+3,a)=
      (27*(27:ℂ)^(-s))*cubicThetaRamifiedTerm s h (e,n,a) := by
  rw [cubicThetaRamifiedTerm_factor,cubicThetaRamifiedTerm_factor,
    cubicThetaRamifiedFactor_cube,cubicThetaPrimaryFourierTerm_cube,mul_assoc]

end CubicFirstMoment

end

end OAI
