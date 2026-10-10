import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeEulerStep
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeLocalCases

namespace OAI

/-! The five possible local rows at a cubically multiplied frequency. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaNormPower_cpow (p d : Eisenstein) (n : ℕ) (s : ℂ) :
    (norm (p^n*d):ℂ)^(-s)=((norm p:ℂ)^(-s))^n*(norm d:ℂ)^(-s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',mul_assoc,norm_mul_eq,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (norm_nonneg p) (norm_nonneg (p^n*d)),ih,pow_succ']
    ring

lemma cubicThetaPrimeFree_cubeFrequency {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaEisensteinGaussCoefficient d.val (p^3*h)=cubicThetaEisensteinGaussCoefficient d.val h := by
  rw [mul_comm (p^3)]
  exact cubicThetaEisensteinGaussCoefficient_cubeFrequency d.property.1 d.property.2.1 hp.1
    (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm h

lemma cubicThetaPrimeFree_phaseCube {p : Eisenstein} (hp : primaryPrime p)
    (d : CubicThetaPrimeFreeDenominator p) :
    (cubicSymbol p (3*d.val)*cubicSymbol p d.val)^3=1 := by
  have hpd : IsCoprime p d.val := hp.2.coprime_iff_not_dvd.mpr d.property.2.2
  have hp3 : IsCoprime p (3:Eisenstein) :=
    (isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hp.1 (dvd_refl p))).symm
  rw [mul_pow,cubicSymbol_cube_of_isCoprime hp.1 _ (hp3.mul_right hpd),
    cubicSymbol_cube_of_isCoprime hp.1 _ hpd,one_mul]

lemma cubicThetaPrimePowerTerm_cube_zero {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p^3*h) (0,d)=cubicThetaPrimeFreeTerm p s h 0 d := by
  rw [cubicThetaPrimePowerTerm_zero]
  unfold cubicThetaPrimeFreeTerm
  rw [cubicThetaPrimeFree_cubeFrequency hp]

lemma cubicThetaPrimePowerTerm_cube_one {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p^3*h) (1,d)=0 := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  change cubicThetaEisensteinGaussCoefficient (p^1*d.val) (p^3*h)*_=0
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp]
  have hz : cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 1 (p^3*h)=0 := by
    convert cubicThetaLocalPrimePowerGauss_prime_multiple hp (p^2*h) using 1
    congr 1
    ring
  rw [hz,mul_zero,zero_mul,zero_mul]

lemma cubicThetaPrimePowerTerm_cube_two {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p^3*h) (2,d)=0 := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  change cubicThetaEisensteinGaussCoefficient (p^2*d.val) (p^3*h)*_=0
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp]
  have hz : cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 2 (p^3*h)=0 := by
    convert cubicThetaLocalPrimePowerGauss_square_multiple hp (p*h) using 1
    congr 1
    ring
  rw [hz,mul_zero,zero_mul,zero_mul]

lemma cubicThetaPrimePowerTerm_cube_three {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p^3*h) (3,d)=
      (norm p:ℂ)^2*((norm p:ℂ)-1)*((norm p:ℂ)^(-s))^3*cubicThetaPrimeFreeTerm p s h 0 d := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  have hG : cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 3 (p^3*h)=
      (norm (p^2):ℂ)*((norm p:ℂ)-1) := by
    convert cubicThetaLocalPrimePowerGauss_cube hp (p*h) using 1
    · congr 1; ring
    · rw [ite_eq_left (dvd_mul_right p h)]
  change cubicThetaEisensteinGaussCoefficient (p^3*d.val) (p^3*h)*
    (norm (p^3*d.val):ℂ)^(-s)= _
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp,
    cubicThetaPrimeFree_phaseCube hp,one_mul,hG,cubicThetaPrimeFree_cubeFrequency hp,
    cubicThetaNormPower_cpow,eisenstein_norm_pow,Complex.ofReal_pow]
  unfold cubicThetaPrimeFreeTerm
  simp only [pow_zero,one_mul]
  ring

lemma cubicThetaEisensteinGaussCoefficient_fourth_cube {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaEisensteinGaussCoefficient (p^4*d.val) (p^3*h)=
      (norm (p^3):ℂ)*cubicThetaEisensteinGaussCoefficient (p*d.val) h := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp,
    show (4:ℕ)=3+1 by omega,pow_succ,cubicThetaPrimeFree_phaseCube hp,one_mul,
    cubicThetaLocalPrimePowerGauss_fourth hp,cubicThetaPrimeFree_cubeFrequency hp,
    cubicThetaEisensteinGaussCoefficient_factor hp.1 d.property.1 d.property.2.1 hcp,
    cubicThetaSymbolFourier_prime hp]
  ring

lemma cubicThetaPrimePowerTerm_cube_four {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p^3*h) (4,d)=
      (norm p:ℂ)^3*((norm p:ℂ)^(-s))^3*cubicThetaPrimePowerTerm p hp s h (1,d) := by
  change cubicThetaEisensteinGaussCoefficient (p^4*d.val) (p^3*h)*
    (norm (p^4*d.val):ℂ)^(-s)=
    _*(cubicThetaEisensteinGaussCoefficient (p^1*d.val) h*(norm (p^1*d.val):ℂ)^(-s))
  rw [cubicThetaEisensteinGaussCoefficient_fourth_cube hp,cubicThetaNormPower_cpow,
    cubicThetaNormPower_cpow,eisenstein_norm_pow,Complex.ofReal_pow,pow_one]
  ring

lemma cubicThetaPrimePowerTerm_cube_high {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (hh : ¬p ∣ h) (n : ℕ) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p^3*h) (n+5,d)=0 := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  change cubicThetaEisensteinGaussCoefficient (p^(n+5)*d.val) (p^3*h)*_=0
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp]
  have hn : ¬p^(n+4) ∣ p^3*h := by
    intro hdiv
    have h4 : p^4 ∣ p^3*h := (pow_dvd_pow p (by omega : 4 ≤ n+4)).trans hdiv
    rw [show (4:ℕ)=3+1 by omega,pow_succ,mul_dvd_mul_iff_left (pow_ne_zero 3 hp.2.ne_zero)] at h4
    exact hh h4
  have hz := cubicThetaLocalPrimePowerGauss_eq_zero hp (n+4) (p^3*h) hn
  rw [show n+5=(n+4)+1 by omega,hz,mul_zero,zero_mul,zero_mul]

end CubicFirstMoment

end

end OAI
