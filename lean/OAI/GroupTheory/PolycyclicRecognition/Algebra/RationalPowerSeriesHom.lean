import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentPowerSeriesEvaluation

namespace OAI

/-! # Rational power-series homomorphisms killed by a power of the variable -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A] (F : PowerSeries ℚ →+* A)

theorem rationalPowerSeriesHom_C (q : ℚ) :
    F (PowerSeries.C q) = algebraMap ℚ A q :=
  F.map_rat_algebraMap q

theorem rationalPowerSeriesHom_polynomial (p : Polynomial ℚ) :
    F (p : PowerSeries ℚ) = Polynomial.aeval (F PowerSeries.X) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.coe_add, map_add, hp, hq]
  | monomial k q =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_X, map_mul, map_pow, rationalPowerSeriesHom_C,
      map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]

omit [Algebra ℚ A] in
theorem rationalPowerSeriesHom_eq_trunc {n : ℕ}
    (hF : F PowerSeries.X ^ n = 0) (f : PowerSeries ℚ) :
    F f = F (PowerSeries.trunc n f : PowerSeries ℚ) := by
  have hd : (PowerSeries.X : PowerSeries ℚ) ^ n ∣
      f - (PowerSeries.trunc n f : PowerSeries ℚ) := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro k hk
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, ite_eq_left hk, sub_self]
  obtain ⟨q, hq⟩ := hd
  have hzero : F (f - (PowerSeries.trunc n f : PowerSeries ℚ)) = 0 := by
    rw [hq, map_mul, map_pow, hF, zero_mul]
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

theorem rationalPowerSeriesHom_eq_aeval_trunc {n : ℕ}
    (hF : F PowerSeries.X ^ n = 0) (f : PowerSeries ℚ) :
    F f = Polynomial.aeval (F PowerSeries.X) (PowerSeries.trunc n f) := by
  rw [rationalPowerSeriesHom_eq_trunc F hF, rationalPowerSeriesHom_polynomial]

end PolycyclicRecognition

end

end OAI
