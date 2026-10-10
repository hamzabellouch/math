import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic

namespace OAI
/-!
# Remainder control for the Selberg square sieve

The estimates here retain the actual local remainder.  In particular no
prime distribution hypothesis is manufactured by passing to square weights.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Problem337.SelbergError

/-- A weighted version of the divisor expansion of the square sieve. -/
theorem sum_lambdaSquared_mul (P : ℕ) (hP : P ≠ 0)
    (lam f : ℕ → ℝ) :
    (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared lam d * f d) =
      ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
        lam a * lam b * f (Nat.lcm a b) := by
  have henlarge (g : ℕ → ℕ → ℕ → ℝ) :
      (∑ d ∈ P.divisors, ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        if d = Nat.lcm a b then g a b d else 0) =
      ∑ d ∈ P.divisors, ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
        if d = Nat.lcm a b then g a b d else 0 := by
    congr! 1 with d hd
    rw [Nat.mem_divisors] at hd
    have heq : ∀ a b, (a ∣ d ∧ b ∣ d ∧ d = Nat.lcm a b) =
        (d = Nat.lcm a b) := by
      simp +contextual [← and_assoc, Nat.dvd_lcm_left, Nat.dvd_lcm_right]
    simp_rw [← Nat.divisors_filter_dvd_of_dvd hd.2 hd.1,
      sum_filter, ite_sum_zero, ← ite_and, heq]
  calc
    _ = ∑ d ∈ P.divisors, ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        if d = Nat.lcm a b then lam a * lam b * f d else 0 := by
      simp [BoundingSieve.lambdaSquared, sum_mul]
    _ = ∑ d ∈ P.divisors, ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
        if d = Nat.lcm a b then lam a * lam b * f d else 0 := henlarge _
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      rw [sum_comm]
      apply sum_congr rfl
      intro b hb
      have hlcm : Nat.lcm a b ∈ P.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.lcm_dvd_iff.mpr
          ⟨Nat.dvd_of_mem_divisors ha, Nat.dvd_of_mem_divisors hb⟩, hP⟩
      rw [sum_ite_eq_of_mem' _ _ _ hlcm]

/-- Absolute square weights are dominated by the square weights of absolute
values.  This inequality does not assume that the original weights are positive. -/
theorem abs_lambdaSquared_le (lam : ℕ → ℝ) (d : ℕ) :
    |BoundingSieve.lambdaSquared lam d| ≤
      BoundingSieve.lambdaSquared (fun n => |lam n|) d := by
  unfold BoundingSieve.lambdaSquared
  calc
    _ ≤ ∑ a ∈ d.divisors, |∑ b ∈ d.divisors,
        if d = Nat.lcm a b then lam a * lam b else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        |if d = Nat.lcm a b then lam a * lam b else 0| := by
      apply sum_le_sum
      intro a ha
      exact abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_ite, abs_mul, abs_zero]

/-- Exact local remainders can be bounded before any uniform estimate is made. -/
theorem errSum_lambdaSquared_le (s : BoundingSieve) (lam : ℕ → ℝ) :
    s.errSum (BoundingSieve.lambdaSquared lam) ≤
      ∑ a ∈ s.prodPrimes.divisors, ∑ b ∈ s.prodPrimes.divisors,
        |lam a| * |lam b| * |s.rem (Nat.lcm a b)| := by
  calc
    _ ≤ ∑ d ∈ s.prodPrimes.divisors,
        BoundingSieve.lambdaSquared (fun n => |lam n|) d * |s.rem d| := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_right (abs_lambdaSquared_le lam d) (abs_nonneg _)
    _ = _ := sum_lambdaSquared_mul s.prodPrimes
      BoundingSieve.prodPrimes_ne_zero _ _

/-- A factorizable local remainder envelope gives the usual weighted L1-square
bound for the square-sieve error. -/
theorem errSum_lambdaSquared_le_sq (s : BoundingSieve) (lam w : ℕ → ℝ)
    (hrem : ∀ a ∈ s.prodPrimes.divisors, ∀ b ∈ s.prodPrimes.divisors,
      |s.rem (Nat.lcm a b)| ≤ w a * w b) :
    s.errSum (BoundingSieve.lambdaSquared lam) ≤
      (∑ d ∈ s.prodPrimes.divisors, |lam d| * w d) ^ 2 := by
  calc
    _ ≤ ∑ a ∈ s.prodPrimes.divisors, ∑ b ∈ s.prodPrimes.divisors,
        |lam a| * |lam b| * |s.rem (Nat.lcm a b)| := errSum_lambdaSquared_le s lam
    _ ≤ ∑ a ∈ s.prodPrimes.divisors, ∑ b ∈ s.prodPrimes.divisors,
        |lam a| * |lam b| * (w a * w b) := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hrem a ha b hb) (by positivity)
    _ = _ := by
      rw [sq, sum_mul_sum]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      ring

end Problem337.SelbergError

end

end OAI
