import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedRowValue

namespace OAI

/-! Cubic inflation at the ramified prime, for every primary part and
with the conductor-zero cases included. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_ramified_cube {u : Eisenstein}
    (hu : primary u) (n : ℕ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient (lambdaE^(n+5)*u) (lambdaE^3*h)=
      27*cubicThetaEisensteinGaussCoefficient (lambdaE^(n+2)*u) h := by
  by_cases hd : lambdaE^n ∣ h
  · obtain ⟨t,rfl⟩ := hd
    have hp : lambdaE^3*(lambdaE^n*t)=lambdaE^(n+3)*t := by rw [pow_add]; ring
    rw [hp,show n+5=(n+3)+2 by omega,
      cubicThetaEisensteinGaussCoefficient_ramified_inflation hu,
      cubicThetaEisensteinGaussCoefficient_ramified_inflation hu]
    have hm : (n+3+2)%3=(n+2)%3 := by omega
    rw [hm]
    have hlam : norm (lambdaE^3)=27 := by
      simp only [norm,Subalgebra.coe_pow,map_pow,lambdaE_coe,traceLambda_normSq]
      norm_num
    have hn : norm (lambdaE^(n+3))=27*norm (lambdaE^n) := by
      rw [pow_add,norm_mul_eq,hlam]
      ring
    rw [hn]
    push_cast
    ring
  · have hn : ¬lambdaE^(n+3) ∣ lambdaE^3*h := by
      intro hx
      have hp : lambdaE^(n+3)=lambdaE^3*lambdaE^n := by rw [pow_add]; ring
      rw [hp,mul_dvd_mul_iff_left (pow_ne_zero _ lambdaE_prime.ne_zero)] at hx
      exact hd hx
    rw [show n+5=(n+3)+2 by omega,
      cubicThetaEisensteinGaussCoefficient_ramified_zero hu (n+3) _ hn,
      cubicThetaEisensteinGaussCoefficient_ramified_zero hu n _ hd,mul_zero]

end CubicFirstMoment

end

end OAI
