import OAI.NumberTheory.Ostmann.Characters.PolynomialGiantTests
import OAI.NumberTheory.Ostmann.Characters.PolynomialValueBounds
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticCoincidences

namespace OAI

/-! # Concrete integer evaluations in the arithmetic coincidence bounds -/

namespace Ostmann

open scoped BigOperators

theorem integerPolynomial_rational_eval {σ : Type*} (x : σ → ℤ)
    (F : MvPolynomial σ ℤ) :
    MvPolynomial.eval (fun i => (x i : ℚ)) (MvPolynomial.map (Int.castRingHom ℚ) F) =
      ((MvPolynomial.eval₂Hom (RingHom.id ℤ) x F : ℤ) : ℚ) := by
  rw [MvPolynomial.eval_map]
  symm
  simpa [Int.castRingHom] using
    (MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℚ) F)

theorem integerPolynomial_rational_zero_iff {σ : Type*} (F : MvPolynomial σ ℤ) :
    MvPolynomial.map (Int.castRingHom ℚ) F = 0 ↔ F = 0 := by
  have hi : Function.Injective (MvPolynomial.map (Int.castRingHom ℚ) :
      MvPolynomial σ ℤ → MvPolynomial σ ℚ) := MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  constructor
  · intro h
    apply hi
    simpa using h
  · intro h
    simp [h]

theorem integerPolynomial_rational_degree {σ : Type*} (F : MvPolynomial σ ℤ) :
    (MvPolynomial.map (Int.castRingHom ℚ) F).totalDegree = F.totalDegree := by
  simp only [MvPolynomial.totalDegree,
    MvPolynomial.support_map_of_injective F (show Function.Injective (Int.castRingHom ℚ) from
      Int.cast_injective)]

/-- A bound on an actual integer test gives the required independent-prime
cardinality bound without a separate polynomial-height hypothesis. -/
theorem int_prime_divisor_card_le (P : Finset ℕ) (z : ℤ) (hz : z ≠ 0)
    (hprime : ∀ p ∈ P, p.Prime) (B H : ℝ) (hB : 0 < B)
    (hsize : ∀ p ∈ P, B ≤ Real.log (p : ℝ)) (hvalue : |(z : ℝ)| ≤ H) :
    ((P.filter fun p => p ∣ z.natAbs).card : ℝ) ≤ Real.log H / B := by
  have hzpos : 0 < z.natAbs := Int.natAbs_pos.mpr hz
  have hcast : (z.natAbs : ℝ) = |(z : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hlog : Real.log (z.natAbs : ℝ) ≤ Real.log H :=
    Real.log_le_log (by exact_mod_cast hzpos) (hcast ▸ hvalue)
  apply prime_divisor_card_le P hzpos hprime B (Real.log H / B) hB hsize
  simpa only [div_mul_cancel₀ _ hB.ne'] using hlog

/-- The common-denominator recurrence yields the logarithmic budget for any
nonzero cleared coefficient with the established power bound. -/
theorem int_prime_divisor_card_le_power (P : Finset ℕ) (z : ℤ) (hz : z ≠ 0)
    (hprime : ∀ p ∈ P, p.Prime) (B H : ℝ) (n : ℕ) (hB : 0 < B)
    (hsize : ∀ p ∈ P, B ≤ Real.log (p : ℝ)) (hvalue : |(z : ℝ)| ≤ H ^ n) :
    ((P.filter fun p => p ∣ z.natAbs).card : ℝ) ≤ (n : ℝ) * Real.log H / B := by
  have h := int_prime_divisor_card_le P z hz hprime B (H ^ n) hB hsize hvalue
  simpa only [Real.log_pow] using h

end Ostmann

end OAI
