import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGaussFactor
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeGauss
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFrequencyTwist

namespace OAI

/-! Local prime-power recurrences for the genuine arithmetic row coefficient. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_primePower {p c : Eisenstein}
    (hp : primaryPrime p) (hc : (3:Eisenstein) ∣ c) (hc0 : c≠0)
    (hcp : IsCoprime c p) (n : ℕ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient (p^n*c) h=
      (cubicSymbol p (3*c)*cubicSymbol p c)^n*
        cubicThetaLocalPrimePowerGauss p hp.2.ne_zero n h*
          cubicThetaEisensteinGaussCoefficient c h := by
  have hpn : primary (p^n) := by
    induction n with
    | zero => simpa using primary_one
    | succ n ih => simpa only [pow_succ] using primary_mul ih hp.1
  rw [cubicThetaEisensteinGaussCoefficient_factor hpn hc hc0 hcp.pow_right,
    cubicThetaSymbol_prime_pow hp,cubicThetaSymbol_prime_pow hp,← mul_pow]
  rfl

lemma cubicThetaSymbolFourier_prime {p : Eisenstein} (hp : primaryPrime p) (h : Eisenstein) :
    cubicThetaSymbolFourier p hp.2.ne_zero h=cubicThetaPrimeFourier p hp 1 h := by
  unfold cubicThetaSymbolFourier cubicThetaPrimeFourier
  apply tsum_congr
  intro x
  rw [pow_one,cubicSymbol_prime hp]
  rfl

theorem cubicThetaEisensteinGaussCoefficient_prime_unit {p c : Eisenstein}
    (hp : primaryPrime p) (hc : (3:Eisenstein) ∣ c) (hc0 : c≠0)
    (hcp : IsCoprime c p) (h : Eisenstein) (hph : IsCoprime p h) :
    cubicThetaEisensteinGaussCoefficient (p*c) h=
      (cubicSymbol p c)^2*star (cubicSymbol p h)*(Real.sqrt (norm p):ℂ)*gauss p*
        cubicThetaEisensteinGaussCoefficient c h := by
  rw [cubicThetaEisensteinGaussCoefficient_factor hp.1 hc hc0 hcp,
    cubicThetaSymbolFourier_prime hp,cubicThetaPrimeFourier_unit hp (by norm_num) h hph,
    pow_one,cubicThetaPrimeFourier_one_one hp,cubicSymbol_mul_upper hp.1]
  have hphase := cubicSymbol_three_lambda hp.1
  rw [cubicSymbol_mul_upper hp.1] at hphase
  calc
    _ = (cubicSymbol p 3*cubicSymbol p lambdaE)*
        ((cubicSymbol p c)^2*star (cubicSymbol p h)*(Real.sqrt (norm p):ℂ)*gauss p*
          cubicThetaEisensteinGaussCoefficient c h) := by ring
    _ = _ := by rw [hphase,one_mul]

theorem cubicThetaEisensteinGaussCoefficient_highPrimePower {p c : Eisenstein}
    (hp : primaryPrime p) (hc : (3:Eisenstein) ∣ c) (hc0 : c≠0)
    (hcp : IsCoprime c p) (n : ℕ) (h : Eisenstein) (hph : ¬p ∣ h) :
    cubicThetaEisensteinGaussCoefficient (p^(n+2)*c) h=0 := by
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp hc hc0 hcp]
  have hpn : ¬p^(n+1) ∣ h := fun hd =>
    hph ((dvd_pow_self p (Nat.succ_ne_zero n)).trans hd)
  have hz := cubicThetaLocalPrimePowerGauss_eq_zero hp (n+1) h hpn
  rw [show n+2=(n+1)+1 by omega,hz,mul_zero,zero_mul]

end CubicFirstMoment

end

end OAI
