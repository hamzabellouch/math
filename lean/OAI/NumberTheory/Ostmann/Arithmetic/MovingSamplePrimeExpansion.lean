import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalSampleExpansion
import OAI.NumberTheory.Ostmann.ZeroDensity.ComplexPrimeWeights

namespace OAI

/-! # The exact sample expansion inside the actual giant-prime averages -/

namespace Ostmann
open scoped Classical BigOperators

theorem complexPrimeInterval_sum {I : Type*} (q a : ℕ) (u v : ℝ)
    (S : Finset I) (F : I → ℝ → ℂ) :
    complexPrimeInterval q a u v (fun x => ∑ i ∈ S, F i x) =
      ∑ i ∈ S, complexPrimeInterval q a u v (F i) := by
  unfold complexPrimeInterval
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : p.Prime ∧ Nat.ModEq q p a
  · simp [h]
  · simp [h]

theorem complexPrimeInterval_const_mul (q a : ℕ) (u v : ℝ) (c : ℂ) (F : ℝ → ℂ) :
    complexPrimeInterval q a u v (fun x => c * F x) =
      c * complexPrimeInterval q a u v F := by
  unfold complexPrimeInterval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp only [mul_assoc, mul_zero]

theorem complexPrimePair_sum {I : Type*} (u v r s : ℝ)
    (S : Finset I) (F : I → ℝ → ℝ → ℂ) :
    complexPrimeInterval 1 0 r s (fun y =>
      complexPrimeInterval 1 0 u v (fun x => ∑ i ∈ S, F i x y)) =
    ∑ i ∈ S, complexPrimeInterval 1 0 r s (fun y =>
      complexPrimeInterval 1 0 u v (fun x => F i x y)) := by
  simp_rw [complexPrimeInterval_sum]

theorem complexPrimePair_const_mul (u v r s : ℝ) (c : ℂ) (F : ℝ → ℝ → ℂ) :
    complexPrimeInterval 1 0 r s (fun y =>
      complexPrimeInterval 1 0 u v (fun x => c * F x y)) =
    c * complexPrimeInterval 1 0 r s (fun y =>
      complexPrimeInterval 1 0 u v (fun x => F x y)) := by
  simp_rw [complexPrimeInterval_const_mul]

/-- No prime asymptotic or independence approximation enters this exchange:
these are finite sums over the original two giant-prime intervals. -/
theorem movingCompensatedAverage_prime_pair_patterns {A : Type*} [Fintype A]
    (μ : ℕ → A → ℝ) (value : A → ℕ) (n : ℕ)
    (H K : ℝ → ℝ → MovingSampleSlots A n → ℂ) (u v r s : ℝ) :
    letI := sampleSetoidFintype (Bool × MovingSampleIndex n)
    complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v (fun x =>
      movingCompensatedAverage μ value n (H x y) *
        star (movingCompensatedAverage μ value n (K x y)))) =
    ∑ eqp : Setoid (Bool × MovingSampleIndex n),
      ∑ z : {z : Quotient eqp → A // Function.Injective z},
        let a := (movingSamplePairCoordinates A n).symm (fun i => z.val (Quotient.mk'' i))
        (internalPatternWeight (fun i => Quotient.mk'' i)
          (fun i => μ (movingSampleTier i.2)) value z.val : ℂ) *
          complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v (fun x =>
            H x y a.1 * star (K x y a.2))) := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  simp_rw [movingCompensatedAverage_pair_patterns, complexPrimeInterval_sum]
  apply Finset.sum_congr rfl
  intro eqp _
  apply Finset.sum_congr rfl
  intro z _
  simp_rw [mul_assoc, complexPrimeInterval_const_mul]

end Ostmann

end OAI
