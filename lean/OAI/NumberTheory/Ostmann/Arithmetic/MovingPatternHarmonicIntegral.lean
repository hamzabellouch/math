import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternCoefficientMass
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimePatternProducts
import OAI.NumberTheory.Ostmann.Arithmetic.HarmonicPairIntegral

namespace OAI

/-! # Passing the signed original-pattern bound through both giant cells -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem movingPattern_prime_harmonic_integral_bound {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (G : (Fin (N + 1) → A) → ℝ → ℝ → ℂ)
    (hG : ∀ x, Measurable (Function.uncurry (G x)))
    (u v r s D : ℝ) (hu : 1 ≤ u) (hr : 1 ≤ r)
    (huv : u ≤ v) (hrs : r ≤ s) (hv : v ≤ u + 1) (hs : s ≤ r + 1) (hD : 0 ≤ D)
    (K : (Fin (N + 1) → A) → ℝ) (hK : ∀ x, 0 ≤ K x)
    (hbound : ∀ x a, a ∈ Set.Ioc u v → ∀ b, b ∈ Set.Ioc r s → ‖G x a b‖ ≤ K x)
    (hmean : ∀ a ∈ Set.Ioc u v, ∀ b ∈ Set.Ioc r s,
      ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern (fun x => G x a b) x *
        movingPatternPrimeHaarProduct e prime hprime n t small bulk pattern x‖ ≤ D) :
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern
        (fun x => ∫ a in Set.Ioc u v, ∫ b in Set.Ioc r s,
          G x a b / ((a : ℂ) * (b : ℂ))) x *
      movingPatternPrimeHaarProduct e prime hprime n t small bulk pattern x‖ ≤ D / (u * r) := by
  let w := movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1)
  let H := movingPatternPrimeHaarProduct e prime hprime n t small bulk pattern
  have hpoint (a : ℝ) (ha : a ∈ Set.Ioc u v) (b : ℝ) (hb : b ∈ Set.Ioc r s) :
      ‖∑ x, w x * (G x a b * H x)‖ ≤ D := by
    have he (x) : movingOriginalPatternWeight e μ ν prime n pattern (fun x => G x a b) x * H x =
        w x * (G x a b * H x) := by
      rw [movingOriginalPatternWeight_eq_coefficient_mul]
      exact mul_assoc _ _ _
    have hm := hmean a ha b hb
    change ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern (fun x => G x a b) x * H x‖ ≤ D at hm
    simpa only [he] using hm
  have h := finite_harmonic_pair_sum_norm u v r s D hu hr huv hrs hv hs hD w
    (fun x a b => G x a b * H x) (fun x => (hG x).mul_const (H x))
    (fun x => K x * ‖H x‖) (fun x => mul_nonneg (hK x) (norm_nonneg _))
    (by
      intro x a ha b hb
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound x a ha b hb) (norm_nonneg _)) hpoint
  have he (x) : movingOriginalPatternWeight e μ ν prime n pattern
        (fun x => ∫ a in Set.Ioc u v, ∫ b in Set.Ioc r s,
          G x a b / ((a : ℂ) * (b : ℂ))) x * H x =
      w x * ∫ a in Set.Ioc u v, ∫ b in Set.Ioc r s,
        (G x a b * H x) / ((a : ℂ) * (b : ℂ)) := by
    rw [movingOriginalPatternWeight_eq_coefficient_mul]
    simp_rw [mul_div_right_comm, integral_mul_const]
    exact mul_assoc _ _ _
  change ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern
    (fun x => ∫ a in Set.Ioc u v, ∫ b in Set.Ioc r s,
      G x a b / ((a : ℂ) * (b : ℂ))) x * H x‖ ≤ _
  simpa only [he] using h

end Ostmann

end OAI
