import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDirichlet

namespace OAI

/-! The exact first local Euler step for a frequency prime to p. The two
remaining series retain their actual cubic twists on the prime-free rows. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeFreeTerm (p : Eisenstein) (s : ℂ) (h : Eisenstein) (j : ℕ)
    (d : CubicThetaPrimeFreeDenominator p) : ℂ :=
  (cubicSymbol p d.val)^j*cubicThetaEisensteinGaussCoefficient d.val h*(norm d.val:ℂ)^(-s)

def cubicThetaPrimeFreeDirichlet (p : Eisenstein) (s : ℂ) (h : Eisenstein) (j : ℕ) : ℂ :=
  ∑' d : CubicThetaPrimeFreeDenominator p, cubicThetaPrimeFreeTerm p s h j d

def cubicThetaPrimeFirstFactor (p : Eisenstein) (s : ℂ) (h : Eisenstein) : ℂ :=
  star (cubicSymbol p h)*(Real.sqrt (norm p):ℂ)*gauss p*(norm p:ℂ)^(-s)

lemma cubicThetaPrimePowerTerm_zero {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s h (0,d)=cubicThetaPrimeFreeTerm p s h 0 d := by
  simp [cubicThetaPrimePowerTerm,cubicThetaDenominatorTerm,cubicThetaPrimePowerDenominator,
    cubicThetaPrimeFreeTerm]

lemma cubicThetaPrimePowerTerm_one {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (hh : ¬p ∣ h) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s h (1,d)=
      cubicThetaPrimeFirstFactor p s h*cubicThetaPrimeFreeTerm p s h 2 d := by
  have hcp : IsCoprime d.val p := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  have hph : IsCoprime p h := hp.2.coprime_iff_not_dvd.mpr hh
  change cubicThetaEisensteinGaussCoefficient (p^1*d.val) h*(norm (p^1*d.val):ℂ)^(-s)=_
  rw [pow_one,cubicThetaEisensteinGaussCoefficient_prime_unit hp d.property.1 d.property.2.1 hcp h hph,
    norm_mul_eq,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (norm_nonneg p) (norm_nonneg d.val)]
  unfold cubicThetaPrimeFirstFactor cubicThetaPrimeFreeTerm
  ring

theorem cubicThetaFrequencyDirichlet_primeEulerStep {p : Eisenstein} (hp : primaryPrime p)
    {s : ℂ} (hs : 2<s.re) (h : Eisenstein) (hh : ¬p ∣ h) :
    cubicThetaFrequencyDirichlet h s=cubicThetaPrimeFreeDirichlet p s h 0+
      cubicThetaPrimeFirstFactor p s h*cubicThetaPrimeFreeDirichlet p s h 2 := by
  rw [cubicThetaFrequencyDirichlet_two_terms hp hs h hh]
  simp_rw [cubicThetaPrimePowerTerm_zero hp,cubicThetaPrimePowerTerm_one hp s h hh]
  rw [tsum_mul_left]
  rfl

end CubicFirstMoment

end

end OAI
