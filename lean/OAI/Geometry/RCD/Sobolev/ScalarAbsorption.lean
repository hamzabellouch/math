import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

open scoped BigOperators

namespace RegularPointCoordinates

/-- The scalar absorption used after testing the radial transport equation. -/
theorem radial_energy_absorption {energy alpha error C : ℝ}
    (henergy : 0 ≤ energy)
    (hbound : energy ≤ C * (alpha ^ 2 + error ^ 2) +
      C * Real.sqrt energy * (alpha + error)) :
    energy ≤ 2 * (C + C ^ 2) * (alpha ^ 2 + error ^ 2) := by
  have hsqrt := Real.sq_sqrt henergy
  have hyoung := sq_nonneg (Real.sqrt energy - C * (alpha + error))
  have hcross := mul_nonneg (sq_nonneg C) (sq_nonneg (alpha - error))
  nlinarith

/-- A contractive recurrence has a uniform finite-scale square-sum estimate.
The extra endpoint term makes the induction telescope without infinite sums. -/
theorem contracting_recurrence_sq_sum {b f : ℕ → ℝ} {C : ℝ}
    (hzero : b 0 = 0) (hpos : ∀ i, 0 ≤ b i)
    (hrec : ∀ i, b (i + 1) ≤ b i / 2 + C * f i) (k : ℕ) :
    (∑ i ∈ Finset.range k, b i ^ 2) + 2 * b k ^ 2 ≤
      4 * C ^ 2 * ∑ i ∈ Finset.range k, f i ^ 2 := by
  induction k with
  | zero => simp [hzero]
  | succ k ih =>
    have hsquare : b (k + 1) ^ 2 ≤ (b k / 2 + C * f k) ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self (hpos (k + 1)) (hrec k)
    have hstep : b (k + 1) ^ 2 ≤ b k ^ 2 / 2 + 2 * C ^ 2 * f k ^ 2 := by
      nlinarith [sq_nonneg (b k / 2 - C * f k)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    nlinarith

/-- The diagonal error estimate used when summing metric increments. -/
theorem contracting_recurrence_sq_sum_le {b f : ℕ → ℝ} {C : ℝ}
    (hzero : b 0 = 0) (hpos : ∀ i, 0 ≤ b i)
    (hrec : ∀ i, b (i + 1) ≤ b i / 2 + C * f i) (k : ℕ) :
    (∑ i ∈ Finset.range k, b i ^ 2) ≤
      4 * C ^ 2 * ∑ i ∈ Finset.range k, f i ^ 2 := by
  have h := contracting_recurrence_sq_sum hzero hpos hrec k
  nlinarith [sq_nonneg (b k)]

/-- The same estimate needs the recurrence only below the scale being tested. -/
theorem contracting_recurrence_sq_sum_upto {b f : ℕ → ℝ} {C : ℝ}
    (k : ℕ) (hzero : b 0 = 0) (hpos : ∀ i, 0 ≤ b i)
    (hrec : ∀ i < k, b (i + 1) ≤ b i / 2 + C * f i) :
    (∑ i ∈ Finset.range k, b i ^ 2) + 2 * b k ^ 2 ≤
      4 * C ^ 2 * ∑ i ∈ Finset.range k, f i ^ 2 := by
  induction k with
  | zero => simp [hzero]
  | succ k ih =>
    have ih' := ih (fun i hi => hrec i (Nat.lt_trans hi (Nat.lt_succ_self k)))
    have hsquare : b (k + 1) ^ 2 ≤ (b k / 2 + C * f k) ^ 2 := by
      simpa only [pow_two] using
        mul_self_le_mul_self (hpos (k + 1)) (hrec k (Nat.lt_succ_self k))
    have hstep : b (k + 1) ^ 2 ≤ b k ^ 2 / 2 + 2 * C ^ 2 * f k ^ 2 := by
      nlinarith [sq_nonneg (b k / 2 - C * f k)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    nlinarith

end RegularPointCoordinates

end OAI
