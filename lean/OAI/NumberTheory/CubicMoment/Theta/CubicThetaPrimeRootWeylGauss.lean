import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeylFormula
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramSinglePrime
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeLocalCases
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeFourierNormalization

namespace OAI

/-! The two axes of the actual Weyl kernel are the cubic Gauss factors.
The inverse-nine twist is retained in the second axis. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeRootWeylKernel_zero_left {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) :
    cubicThetaPrimeRootWeylKernel hp 0 (Ideal.Quotient.mk (modulus p) h)=
      cubicThetaPrimeFourier p hp 1 (-h) := by
  rw [cubicThetaPrimeRootWeylKernel_kloosterman, neg_zero, zero_mul,
    ←map_neg, cubicThetaSymbolKloosterman_prime_zero hp]

lemma cubicThetaPrimeRootWeylKernel_zero_right {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) :
    cubicThetaPrimeRootWeylKernel hp (Ideal.Quotient.mk (modulus p) (9*h)) 0=
      star (cubicThetaPrimeFourier p hp 1 h) := by
  have he : -(Ideal.Quotient.mk (modulus p) (9*h))*
      Ring.inverse (Ideal.Quotient.mk (modulus p) 9)=
        -(Ideal.Quotient.mk (modulus p) h) := by
    rw [map_mul]
    calc
      _ = -(Ideal.Quotient.mk (modulus p) h)*
          (Ring.inverse (Ideal.Quotient.mk (modulus p) 9)*
            Ideal.Quotient.mk (modulus p) 9) := by ring
      _ = _ := by rw [Ring.inverse_mul_cancel _ (cubicThetaPrimeRoot_nine_unit hp),mul_one]
  rw [cubicThetaPrimeRootWeylKernel_kloosterman,neg_zero,he,
    cubicThetaSymbolKloosterman_hermitian hp.1,neg_neg,neg_zero,
    cubicThetaSymbolKloosterman_prime_zero hp]

lemma cubicThetaPrimeRootWeylKernel_zero_zero {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeRootWeylKernel hp 0 0=0 := by
  have he := cubicThetaPrimeRootWeylKernel_zero_left hp 0
  simpa only [map_zero,neg_zero,mul_zero] using
    he.trans (by simpa only [mul_zero,neg_zero] using cubicThetaPrimeFourier_one_multiple hp 0)

lemma cubicThetaPrimeFourier_one_norm {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) :
    ‖cubicThetaPrimeFourier p hp 1 h‖=Real.sqrt (norm p) := by
  rw [cubicThetaPrimeFourier_unit hp (by decide) h hh,pow_one,
    cubicThetaPrimeFourier_one_one hp,norm_mul,norm_star,
    norm_cubicSymbol_of_isCoprime hp.1 hh,norm_mul,norm_mul,
    norm_cubicSymbol_of_isCoprime hp.1 (primary_coprime_lambda hp.1),
    gauss_prime hp,norm_gaussAtPrime hp,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),one_mul,mul_one,one_mul]

theorem cubicThetaPrimeRootWeylKernel_zero_left_additive {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : IsCoprime p h) :
    cubicSymbol p 3*cubicThetaPrimeRootWeylKernel hp 0 (Ideal.Quotient.mk (modulus p) h)=
      cubicThetaPrimeAdditiveGauss p hp 1 (-h) := by
  rw [cubicThetaPrimeRootWeylKernel_zero_left,
    cubicThetaPrimeCubeFirstFourier_additive hp (-h) hh.neg_right]

theorem cubicThetaPrimeRootWeylKernel_zero_left_norm {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : IsCoprime p h) :
    ‖cubicThetaPrimeRootWeylKernel hp 0 (Ideal.Quotient.mk (modulus p) h)‖=
      Real.sqrt (norm p) := by
  rw [cubicThetaPrimeRootWeylKernel_zero_left]
  exact cubicThetaPrimeFourier_one_norm hp (-h) hh.neg_right

theorem cubicThetaPrimeRootWeylKernel_zero_right_norm {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : IsCoprime p h) :
    ‖cubicThetaPrimeRootWeylKernel hp (Ideal.Quotient.mk (modulus p) (9*h)) 0‖=
      Real.sqrt (norm p) := by
  rw [cubicThetaPrimeRootWeylKernel_zero_right,norm_star]
  exact cubicThetaPrimeFourier_one_norm hp h hh

end CubicFirstMoment

end

end OAI
