import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeKloostermanInflation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeLocalCases

namespace OAI

/-! Exact zero-phase factors at the first three prime powers. These are
used for the lower layers when both Gram frequencies contain a cube. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimeKloosterman_multiple {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (h k : Eisenstein) :
    cubicThetaPrimeKloosterman p hp n (p*h) (p*k)=cubicThetaPrimeFourier p hp n 0 := by
  have hz (a : Eisenstein) : Ideal.Quotient.mk (modulus p) (p*a)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right p a))
  unfold cubicThetaPrimeKloosterman cubicThetaPrimeFourier
  apply tsum_congr
  intro x
  simp only [hz,map_zero,zero_mul,zero_add]

lemma cubicThetaSymbolKloosterman_zero_indices {p : Eisenstein}
    (hp : primaryPrime p) (n : ℕ) :
    cubicThetaSymbolKloosterman (p^(n+1)) (pow_ne_zero _ hp.2.ne_zero) 0 0=
      (norm (p^n):ℂ)*cubicThetaPrimeFourier p hp (n+1) 0 := by
  have he := cubicThetaPrimeKloosterman_reduction hp n (p*0) (p*0)
  rw [cubicThetaPrimeKloosterman_multiple hp] at he
  simpa only [mul_zero,map_zero] using he

lemma cubicThetaSymbolKloosterman_prime_origin {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSymbolKloosterman p hp.2.ne_zero 0 0=0 := by
  have he := cubicThetaSymbolKloosterman_zero_indices hp 0
  have hz : cubicThetaPrimeFourier p hp 1 0=0 := by
    simpa only [mul_zero] using cubicThetaPrimeFourier_one_multiple hp 0
  change cubicThetaSymbolKloosterman (p^1) (pow_ne_zero _ hp.2.ne_zero) 0 0=_ at he
  have hc (q : Eisenstein) (hq : q≠0) (eq : q=p) :
      cubicThetaSymbolKloosterman q hq 0 0=cubicThetaSymbolKloosterman p hp.2.ne_zero 0 0 := by
    subst q
    rfl
  rw [hc _ _ (pow_one p)] at he
  simpa only [hz,mul_zero] using he

lemma cubicThetaSymbolKloosterman_square_zero {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSymbolKloosterman (p^2) (pow_ne_zero _ hp.2.ne_zero) 0 0=0 := by
  have he := cubicThetaSymbolKloosterman_zero_indices hp 1
  have hz : cubicThetaPrimeFourier p hp 2 0=0 := by
    simpa only [mul_zero] using cubicThetaPrimeFourier_two_multiple hp 0
  simpa only [hz,mul_zero] using he

lemma cubicThetaSymbolKloosterman_cube_zero {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSymbolKloosterman (p^3) (pow_ne_zero _ hp.2.ne_zero) 0 0=
      (norm (p^2):ℂ)*((norm p:ℂ)-1) := by
  rw [cubicThetaSymbolKloosterman_zero_indices hp 2,cubicThetaPrimeFourier_three hp,
    ite_eq_left (dvd_zero p)]

end CubicFirstMoment

end

end OAI
