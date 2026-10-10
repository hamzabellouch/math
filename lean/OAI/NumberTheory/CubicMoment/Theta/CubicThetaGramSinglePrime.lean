import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSymbolKloostermanSymmetry
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeGauss

namespace OAI

/-! The single-prime denominator layer in the actual off-diagonal Gram
kernel is exactly the previously normalized cubic Gauss factor. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaSymbolKloosterman_prime_zero {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) :
    cubicThetaSymbolKloosterman p hp.2.ne_zero (Ideal.Quotient.mk (modulus p) h) 0=
      cubicThetaPrimeFourier p hp 1 h := by
  unfold cubicThetaSymbolKloosterman cubicThetaPrimeFourier
  apply tsum_congr
  intro x
  simp only [zero_mul,add_zero,pow_one]
  have he := cubicResidueChar_mk p hp (residueRepresentative p x)
  rw [residueRepresentative_spec,←cubicSymbol_prime hp] at he
  rw [he]

theorem cubicThetaKloostermanSum_single_prime {p c : Eisenstein}
    (hp : primaryPrime p) (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (hcp : IsCoprime c p)
    (h k : Eisenstein) :
    cubicThetaKloostermanSum h (p*k) (p*c) (dvd_mul_of_dvd_right hc p)=
      (cubicSymbol p (3*c)*cubicSymbol p c)*cubicThetaPrimeFourier p hp 1 h*
        cubicThetaFiniteKloosterman c hc0 (Ideal.Quotient.mk (modulus (3*c)) h)
          (Ideal.Quotient.mk (modulus (3*c)) (p*k)*
            (Ring.inverse (Ideal.Quotient.mk (modulus (3*c)) p))^2) := by
  have hz : Ideal.Quotient.mk (modulus p) p=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_refl p))
  rw [cubicThetaKloostermanSum_factor hp.1 hc hc0 hcp,map_mul,hz,zero_mul,zero_mul,
    cubicThetaSymbolKloosterman_prime_zero hp]

theorem cubicThetaKloostermanSum_single_prime_gauss {p c : Eisenstein}
    (hp : primaryPrime p) (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (hcp : IsCoprime c p)
    (h k : Eisenstein) (hh : IsCoprime p h) :
    cubicThetaKloostermanSum h (p*k) (p*c) (dvd_mul_of_dvd_right hc p)=
      (cubicSymbol p (3*c)*cubicSymbol p c)*
        (star (cubicSymbol p h)*(cubicSymbol p lambdaE*(Real.sqrt (norm p):ℂ)*gauss p))*
        cubicThetaFiniteKloosterman c hc0 (Ideal.Quotient.mk (modulus (3*c)) h)
          (Ideal.Quotient.mk (modulus (3*c)) (p*k)*
            (Ring.inverse (Ideal.Quotient.mk (modulus (3*c)) p))^2) := by
  rw [cubicThetaKloostermanSum_single_prime hp hc hc0 hcp,
    cubicThetaPrimeFourier_unit hp (by decide) h hh,cubicThetaPrimeFourier_one_one hp,pow_one]

end CubicFirstMoment

end

end OAI
