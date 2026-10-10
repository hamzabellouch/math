import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeShiftRows

namespace OAI

/-! Exact rows at the square-divisible frequency. The remaining twisted
series is explicit; vanishing of its residue is not presumed. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimeFree_squareFrequency {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaEisensteinGaussCoefficient d.val (p^2*h)=
      cubicSymbol p d.val*cubicThetaEisensteinGaussCoefficient d.val h := by
  have hp2 : primary (p^2) := by simpa only [pow_two] using primary_mul hp.1 hp.1
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  rw [mul_comm (p^2),cubicThetaEisensteinGaussCoefficient_mul d.property.1 d.property.2.1
    hp2 hcp.pow_right,cubicThetaSymbol_prime_pow hp,cubicSymbol_sq_eq_star hp.1,star_star]

lemma cubicThetaPrimePowerTerm_square_zero {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p^2*h) (0,d)=cubicThetaPrimeFreeTerm p s h 1 d := by
  rw [cubicThetaPrimePowerTerm_zero]
  unfold cubicThetaPrimeFreeTerm
  rw [pow_zero,one_mul,pow_one,cubicThetaPrimeFree_squareFrequency hp]

lemma cubicThetaPrimePowerTerm_square_one {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p^2*h) (1,d)=0 := by
  have he : p^2*h=p*(p*h) := by ring
  rw [he,cubicThetaPrimePowerTerm_prime_one hp]

lemma cubicThetaPrimePowerTerm_square_two {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p^2*h) (2,d)=0 := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  change cubicThetaEisensteinGaussCoefficient (p^2*d.val) (p^2*h)*_=0
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp,
    cubicThetaLocalPrimePowerGauss_square_multiple hp,mul_zero,zero_mul,zero_mul]

lemma cubicThetaPrimePowerTerm_square_three {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (hh : ¬p ∣ h) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p^2*h) (3,d)=
      -((norm p:ℂ)^2*((norm p:ℂ)^(-s))^3)*cubicThetaPrimeFreeTerm p s h 1 d := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  change cubicThetaEisensteinGaussCoefficient (p^3*d.val) (p^2*h)*
    (norm (p^3*d.val):ℂ)^(-s)=_
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp,
    cubicThetaPrimeFree_phaseCube hp,one_mul,cubicThetaLocalPrimePowerGauss_cube hp,
    ite_eq_right hh,cubicThetaPrimeFree_squareFrequency hp,cubicThetaNormPower_cpow,
    eisenstein_norm_pow,Complex.ofReal_pow]
  unfold cubicThetaPrimeFreeTerm
  simp only [pow_one]
  ring

lemma cubicThetaPrimePowerTerm_square_high {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (hh : ¬p ∣ h) (n : ℕ) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p^2*h) (n+4,d)=0 := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  change cubicThetaEisensteinGaussCoefficient (p^(n+4)*d.val) (p^2*h)*_=0
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp]
  have hn : ¬p^(n+3) ∣ p^2*h := by
    intro hd
    have h3 : p^3 ∣ p^2*h := (pow_dvd_pow p (by omega : 3 ≤ n+3)).trans hd
    rw [show (3:ℕ)=2+1 by omega,pow_succ,
      mul_dvd_mul_iff_left (pow_ne_zero 2 hp.2.ne_zero)] at h3
    exact hh h3
  have hz := cubicThetaLocalPrimePowerGauss_eq_zero hp (n+3) (p^2*h) hn
  rw [show n+4=(n+3)+1 by omega,hz,mul_zero,zero_mul,zero_mul]

theorem cubicThetaFrequencyDirichlet_primeSquare {p : Eisenstein}
    (hp : primaryPrime p) {s : ℂ} (hs : 2<s.re) (h : Eisenstein) (hh : ¬p ∣ h) :
    cubicThetaFrequencyDirichlet (p^2*h) s=
      (1-(norm p:ℂ)^2*((norm p:ℂ)^(-s))^3)*cubicThetaPrimeFreeDirichlet p s h 1 := by
  rw [cubicThetaFrequencyDirichlet_primePowers_iterated hp hs]
  rw [tsum_eq_sum (s:=Finset.range 4)]
  · simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    simp_rw [cubicThetaPrimePowerTerm_square_zero hp,cubicThetaPrimePowerTerm_square_one hp,
      cubicThetaPrimePowerTerm_square_two hp,cubicThetaPrimePowerTerm_square_three hp s h hh]
    simp only [tsum_zero,add_zero,tsum_mul_left]
    unfold cubicThetaPrimeFreeDirichlet
    ring
  · intro n hn
    have hn4 : 4 ≤ n := by simpa only [Finset.mem_range,not_lt] using hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn4
    have hz (d : CubicThetaPrimeFreeDenominator p) :
        cubicThetaPrimePowerTerm p hp s (p^2*h) (4+k,d)=0 := by
      simpa only [add_comm 4 k] using cubicThetaPrimePowerTerm_square_high hp s h hh k d
    simp only [hz,tsum_zero]

end CubicFirstMoment

end

end OAI
