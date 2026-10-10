import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRows

namespace OAI

/-! The three possible rows when a prime-free frequency is multiplied by
one primary prime. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimeFree_primeFrequency {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaEisensteinGaussCoefficient d.val (p*h)=
      star (cubicSymbol p d.val)*cubicThetaEisensteinGaussCoefficient d.val h := by
  rw [mul_comm p h]
  exact cubicThetaEisensteinGaussCoefficient_mul d.property.1 d.property.2.1 hp.1
    (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm h

lemma cubicThetaPrimeFree_unit {p : Eisenstein} (hp : primaryPrime p)
    (d : CubicThetaPrimeFreeDenominator p) :
    cubicSymbol p d.val*star (cubicSymbol p d.val)=1 := by
  rw [Complex.star_def,Complex.mul_conj',norm_cubicSymbol_of_isCoprime hp.1
    (hp.2.coprime_iff_not_dvd.mpr d.property.2.2)]
  norm_num

lemma cubicThetaPrimePowerTerm_prime_zero {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p*h) (0,d)=cubicThetaPrimeFreeTerm p s h 2 d := by
  rw [cubicThetaPrimePowerTerm_zero]
  unfold cubicThetaPrimeFreeTerm
  rw [pow_zero,one_mul,cubicThetaPrimeFree_primeFrequency hp,cubicSymbol_sq_eq_star hp.1]

lemma cubicThetaPrimePowerTerm_prime_one {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p*h) (1,d)=0 := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  change cubicThetaEisensteinGaussCoefficient (p^1*d.val) (p*h)*_=0
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp,
    cubicThetaLocalPrimePowerGauss_prime_multiple hp,mul_zero,zero_mul,zero_mul]

lemma cubicThetaPrimeFree_secondPhase {p : Eisenstein} (hp : primaryPrime p)
    (d : CubicThetaPrimeFreeDenominator p) :
    (cubicSymbol p (3*d.val)*cubicSymbol p d.val)^2*
      star (cubicSymbol p lambdaE)*star (cubicSymbol p d.val)=1 := by
  rw [cubicSymbol_mul_upper hp.1,mul_pow,mul_pow,cubicSymbol_sq_eq_star hp.1]
  have hd := cubicThetaPrimeFree_unit hp d
  have hl := congrArg star (cubicSymbol_three_lambda hp.1)
  rw [cubicSymbol_mul_upper hp.1,star_mul,star_one] at hl
  calc
    _ = (star (cubicSymbol p 3)*star (cubicSymbol p lambdaE))*
        (cubicSymbol p d.val*star (cubicSymbol p d.val))^2 := by
      rw [← cubicSymbol_sq_eq_star hp.1 d.val]
      ring
    _ = 1 := by rw [mul_comm (star (cubicSymbol p 3)),hl,hd]; norm_num

lemma cubicThetaEisensteinGaussCoefficient_second_prime {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p ∣ h)
    (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaEisensteinGaussCoefficient (p^2*d.val) (p*h)=
      (norm p:ℂ)*cubicSymbol p h*(Real.sqrt (norm p):ℂ)*star (gauss p)*
        cubicThetaEisensteinGaussCoefficient d.val h := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  have hG : cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 2 (p*h)=
      (norm p:ℂ)*cubicThetaPrimeFourier p hp 2 h := by
    have he := cubicThetaLocalPrimePowerGauss_reduction hp 1 h
    change cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 2 (p^1*h)=
      (norm (p^1):ℂ)*cubicThetaPrimeFourier p hp 2 h at he
    simpa only [pow_one] using he
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp,
    hG,cubicThetaPrimeFourier_two_unit hp h (hp.2.coprime_iff_not_dvd.mpr hh),
    cubicThetaPrimeFourier_one_one hp,cubicThetaPrimeFree_primeFrequency hp]
  have hsqrt : star (Real.sqrt (norm p):ℂ)=(Real.sqrt (norm p):ℂ) := by simp
  simp only [star_mul,hsqrt]
  calc
    _ = ((cubicSymbol p (3*d.val)*cubicSymbol p d.val)^2*
        star (cubicSymbol p lambdaE)*star (cubicSymbol p d.val))*
        ((norm p:ℂ)*cubicSymbol p h*(Real.sqrt (norm p):ℂ)*star (gauss p)*
          cubicThetaEisensteinGaussCoefficient d.val h) := by ring
    _ = _ := by rw [cubicThetaPrimeFree_secondPhase hp,one_mul]

def cubicThetaPrimeSecondFactor (p : Eisenstein) (s : ℂ) (h : Eisenstein) : ℂ :=
  (norm p:ℂ)*cubicSymbol p h*(Real.sqrt (norm p):ℂ)*star (gauss p)*((norm p:ℂ)^(-s))^2

lemma cubicThetaPrimePowerTerm_prime_two {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (hh : ¬p ∣ h) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p*h) (2,d)=
      cubicThetaPrimeSecondFactor p s h*cubicThetaPrimeFreeTerm p s h 0 d := by
  change cubicThetaEisensteinGaussCoefficient (p^2*d.val) (p*h)*
    (norm (p^2*d.val):ℂ)^(-s)=_
  rw [cubicThetaEisensteinGaussCoefficient_second_prime hp h hh d,cubicThetaNormPower_cpow]
  unfold cubicThetaPrimeSecondFactor cubicThetaPrimeFreeTerm
  simp only [pow_zero,one_mul]
  ring

lemma cubicThetaPrimePowerTerm_prime_high {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (hh : ¬p ∣ h) (n : ℕ) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p*h) (n+3,d)=0 := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  change cubicThetaEisensteinGaussCoefficient (p^(n+3)*d.val) (p*h)*_=0
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp]
  have hn : ¬p^(n+2) ∣ p*h := by
    intro hd
    have h2 : p^2 ∣ p*h := (pow_dvd_pow p (by omega : 2 ≤ n+2)).trans hd
    have he : p^2=p*p := pow_two p
    rw [he,mul_dvd_mul_iff_left hp.2.ne_zero] at h2
    exact hh h2
  have hz := cubicThetaLocalPrimePowerGauss_eq_zero hp (n+2) (p*h) hn
  rw [show n+3=(n+2)+1 by omega,hz,mul_zero,zero_mul,zero_mul]

end CubicFirstMoment

end

end OAI
