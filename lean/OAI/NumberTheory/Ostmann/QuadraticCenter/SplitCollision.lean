import OAI.NumberTheory.Ostmann.Preliminaries.WeightedCollision

namespace OAI

/-!
# The final split-prime collision contradiction

Finite quantitative form of the last step in Proposition 3.1. The inputs
about which primes split and the root populations are intermediate claims
of that proposition, not published inputs and not asserted here.
-/

namespace Ostmann

open scoped BigOperators

/-- Split primes double the universal lower bound for the combined collision
probability of the two root populations. -/
theorem split_collision_lower_bound (P R : Finset ℕ) (β₁ β₂ : ℕ → ℝ)
    (hRP : R ⊆ P) (hP : ∀ p ∈ P, p.Prime)
    (hbase : ∀ p ∈ P, 2 / (p : ℝ) ≤ β₁ p + β₂ p)
    (hsplit : ∀ p ∈ R, 4 / (p : ℝ) ≤ β₁ p + β₂ p) :
    2 * (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) +
      2 * (∑ p ∈ R, Real.log (p : ℝ) / (p : ℝ)) ≤
      ∑ p ∈ P, Real.log (p : ℝ) * (β₁ p + β₂ p) := by
  classical
  have hindicator :
      (∑ p ∈ P, if p ∈ R then Real.log (p : ℝ) / (p : ℝ) else 0) =
      ∑ p ∈ R, Real.log (p : ℝ) / (p : ℝ) := by
    rw [← Finset.sum_filter]
    congr 1
    exact Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr hRP)
  calc
    _ = ∑ p ∈ P, Real.log (p : ℝ) *
        (2 / (p : ℝ) + if p ∈ R then 2 / (p : ℝ) else 0) := by
      simp_rw [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
      have hfirst : (∑ p ∈ P, Real.log (p : ℝ) * (2 / (p : ℝ))) =
          2 * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      have hsecond : (∑ p ∈ P,
          if p ∈ R then Real.log (p : ℝ) * (2 / (p : ℝ)) else 0) =
          2 * ∑ p ∈ R, Real.log (p : ℝ) / (p : ℝ) := by
        rw [← hindicator, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        split_ifs <;> ring
      rw [hfirst, hsecond]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left _
        (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le))
      by_cases hpr : p ∈ R
      · simp only [hpr, ite_true]
        calc
          2 / (p : ℝ) + 2 / (p : ℝ) = 4 / (p : ℝ) := by ring
          _ ≤ β₁ p + β₂ p := hsplit p hpr
      · simp only [hpr, ite_false, add_zero]
        exact hbase p hp

/-- Explicit constants for the collision contradiction in Proposition 3.1.
Once the asymptotic errors are at most `L/100`, the log scale is bounded by
`50 C`; hence these hypotheses cannot persist on unbounded scales. -/
theorem split_collision_scale_bound (P R : Finset ℕ) (β₁ β₂ : ℕ → ℝ)
    (L η C : ℝ) (hRP : R ⊆ P) (hP : ∀ p ∈ P, p.Prime)
    (hbase : ∀ p ∈ P, 2 / (p : ℝ) ≤ β₁ p + β₂ p)
    (hsplit : ∀ p ∈ R, 4 / (p : ℝ) ≤ β₁ p + β₂ p)
    (hL : 0 ≤ L) (hη : η ≤ 1 / 1000)
    (hmertens : (1 / 2 - 5 * η) * L - C ≤
      ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ))
    (hsplitmass : (3 / 100) * L ≤ ∑ p ∈ R, Real.log (p : ℝ) / (p : ℝ))
    (hupper : (∑ p ∈ P, Real.log (p : ℝ) * (β₁ p + β₂ p)) ≤ (101 / 100) * L) :
    L ≤ 50 * C := by
  have hlower := split_collision_lower_bound P R β₁ β₂ hRP hP hbase hsplit
  have hηL := mul_le_mul_of_nonneg_right hη hL
  nlinarith

end Ostmann

end OAI
