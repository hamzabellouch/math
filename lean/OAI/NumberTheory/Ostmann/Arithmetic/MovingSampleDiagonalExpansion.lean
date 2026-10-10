import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalPrimeExpansion
import OAI.NumberTheory.Ostmann.Arithmetic.IntegerIntervalVariation

namespace OAI

/-! # Exact sample expansion in the mixed prime/integer diagonal -/

namespace Ostmann
open scoped Classical BigOperators

theorem complexIntegerInterval_sum {I : Type*} (q a : ℕ) (u v G : ℝ)
    (S : Finset I) (F : I → ℝ → ℂ) :
    complexIntegerInterval q a u v G (fun x => ∑ i ∈ S, F i x) =
      ∑ i ∈ S, complexIntegerInterval q a u v G (F i) := by
  unfold complexIntegerInterval
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

theorem complexIntegerInterval_const_mul (q a : ℕ) (u v G : ℝ)
    (c : ℂ) (F : ℝ → ℂ) :
    complexIntegerInterval q a u v G (fun x => c * F x) =
      c * complexIntegerInterval q a u v G F := by
  unfold complexIntegerInterval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact mul_assoc _ _ _

/-- The outer factor may contain the full cutoff weight and the common
regular transform. It depends on the external draws, not the internal pair. -/
theorem movingCompensatedAverage_diagonal_patterns {A : Type*} [Fintype A]
    (μ : ℕ → A → ℝ) (value : A → ℕ) (n : ℕ)
    (H K : ℝ → ℝ → MovingSampleSlots A n → ℂ)
    (W : ℝ → ℝ → ℂ) (u v r s center : ℝ) :
    letI := sampleSetoidFintype (Bool × MovingSampleIndex n)
    complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v center (fun x =>
      (movingCompensatedAverage μ value n (H x y) *
        star (movingCompensatedAverage μ value n (K x y))) * W x y)) =
    ∑ eqp : Setoid (Bool × MovingSampleIndex n),
      ∑ z : {z : Quotient eqp → A // Function.Injective z},
        let a := (movingSamplePairCoordinates A n).symm (fun i => z.val (Quotient.mk'' i))
        (internalPatternWeight (fun i => Quotient.mk'' i)
          (fun i => μ (movingSampleTier i.2)) value z.val : ℂ) *
          complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v center
            (fun x => (H x y a.1 * star (K x y a.2)) * W x y)) := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  simp_rw [movingCompensatedAverage_pair_patterns, Finset.sum_mul,
    complexIntegerInterval_sum, complexPrimeInterval_sum]
  apply Finset.sum_congr rfl
  intro eqp _
  apply Finset.sum_congr rfl
  intro z _
  simp_rw [mul_assoc, complexIntegerInterval_const_mul, complexPrimeInterval_const_mul]

end Ostmann

end OAI
