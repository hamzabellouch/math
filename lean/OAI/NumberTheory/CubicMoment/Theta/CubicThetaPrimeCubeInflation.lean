import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRows

namespace OAI

/-! Cubic inflation of every positive local row, without a restriction
on the valuation of the frequency. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaLocalPrimePowerGauss_cubeInflation {p : Eisenstein}
    (hp : primaryPrime p) (n : ℕ) (h : Eisenstein) :
    cubicThetaLocalPrimePowerGauss p hp.2.ne_zero (n+4) (p^3*h)=
      (norm p:ℂ)^3*cubicThetaLocalPrimePowerGauss p hp.2.ne_zero (n+1) h := by
  by_cases hd : p^n ∣ h
  · obtain ⟨k,rfl⟩ := hd
    have he : p^3*(p^n*k)=p^(n+3)*k := by rw [pow_add]; ring
    rw [he,show n+4=(n+3)+1 by omega,cubicThetaLocalPrimePowerGauss_reduction hp,
      cubicThetaLocalPrimePowerGauss_reduction hp]
    change (norm (p^(n+3)):ℂ)*cubicThetaPrimeFourier p hp ((n+1)+3) k=
      (norm p:ℂ)^3*((norm (p^n):ℂ)*cubicThetaPrimeFourier p hp (n+1) k)
    rw [cubicThetaPrimeFourier_period hp (by omega),eisenstein_norm_pow,eisenstein_norm_pow,
      Complex.ofReal_pow,Complex.ofReal_pow,pow_add]
    ring
  · have hhigh : ¬p^(n+3) ∣ p^3*h := by
      intro he
      rw [show n+3=3+n by omega,pow_add,mul_dvd_mul_iff_left (pow_ne_zero 3 hp.2.ne_zero)] at he
      exact hd he
    rw [show n+4=(n+3)+1 by omega,cubicThetaLocalPrimePowerGauss_eq_zero hp (n+3) _ hhigh,
      cubicThetaLocalPrimePowerGauss_eq_zero hp n _ hd,mul_zero]

theorem cubicThetaEisensteinGaussCoefficient_cubeInflation {p : Eisenstein}
    (hp : primaryPrime p) (n : ℕ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaEisensteinGaussCoefficient (p^(n+4)*d.val) (p^3*h)=
      (norm p:ℂ)^3*cubicThetaEisensteinGaussCoefficient (p^(n+1)*d.val) h := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp,
    cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp,
    cubicThetaLocalPrimePowerGauss_cubeInflation hp,cubicThetaPrimeFree_cubeFrequency hp,
    show n+4=(n+1)+3 by omega,pow_add,cubicThetaPrimeFree_phaseCube hp,mul_one]
  ring

theorem cubicThetaPrimePowerTerm_cubeInflation {p : Eisenstein}
    (hp : primaryPrime p) (s : ℂ) (n : ℕ) (h : Eisenstein)
    (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p^3*h) (n+4,d)=
      (norm p:ℂ)^3*((norm p:ℂ)^(-s))^3*cubicThetaPrimePowerTerm p hp s h (n+1,d) := by
  change cubicThetaEisensteinGaussCoefficient (p^(n+4)*d.val) (p^3*h)*
    (norm (p^(n+4)*d.val):ℂ)^(-s)=
      _*(cubicThetaEisensteinGaussCoefficient (p^(n+1)*d.val) h*
        (norm (p^(n+1)*d.val):ℂ)^(-s))
  rw [cubicThetaEisensteinGaussCoefficient_cubeInflation hp,
    cubicThetaNormPower_cpow,cubicThetaNormPower_cpow,
    show n+4=(n+1)+3 by omega,pow_add]
  ring

end CubicFirstMoment

end

end OAI
