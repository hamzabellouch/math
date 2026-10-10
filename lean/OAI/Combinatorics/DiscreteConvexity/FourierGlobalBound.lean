import OAI.Combinatorics.DiscreteConvexity.FourierProductKernel
import OAI.Combinatorics.DiscreteConvexity.FiniteParseval
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Biased Parseval and the global weight bound

The exact Parseval multiplier for the unnormalized coefficients is
`(q / (1-q))^|U|`. The desired multiplier `q^|U|` is smaller for `0 < q < 1`.
The actual product-kernel identity proves Parseval here; it is not a hypothesis
of the global bound or its family-indicator specialization.
-/

noncomputable section
open scoped BigOperators

namespace TalagrandDiscreteConvexity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Square-root-free biased Parseval for the actual alternating coefficients. -/
theorem biased_parseval (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (f : (V → Bool) → ℝ) :
    (∑ U : Finset V, (q / (1 - q)) ^ U.card * w q f U) =
      cubeExpectation q (fun x => (f x) ^ 2) := by
  simpa only [b, w, cubeExpectation] using
    weighted_kernel_parseval (rowKernel q)
      (fun U : Finset V => (q / (1 - q)) ^ U.card)
      (cubeWeight q) (rowKernel_gram q hq0 hq1) f

theorem weight_sum_le_second_moment (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (f : (V → Bool) → ℝ) :
    (∑ U : Finset V, q ^ U.card * w q f U) ≤
      cubeExpectation q (fun x => (f x) ^ 2) := by
  rw [← biased_parseval q hq0 hq1 f]
  have hratio : q ≤ q / (1 - q) := by
    apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
    nlinarith [sq_nonneg q]
  apply Finset.sum_le_sum
  intro U _
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hq0.le hratio U.card) (w_nonneg q f U)

/-- A bounded-square function has global weight sum at most one. -/
theorem global_weight_bound (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (f : (V → Bool) → ℝ) (hf : ∀ x, (f x) ^ 2 ≤ 1) :
    (∑ U : Finset V, q ^ U.card * w q f U) ≤ 1 := by
  apply (weight_sum_le_second_moment q hq0 hq1 f).trans
  calc
    cubeExpectation q (fun x => (f x) ^ 2) ≤
        ∑ x : V → Bool, cubeWeight q x := by
      unfold cubeExpectation
      apply Finset.sum_le_sum
      intro x _
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hf x) (cubeWeight_nonneg hq0.le hq1.le x)
    _ = 1 := cubeWeight_sum q

/-- The global weight bound for the actual indicator of an arbitrary family.
No monotonicity or density assumption on the family is needed. -/
theorem indicator_global_weight_bound (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (D : Family V) :
    (∑ U : Finset V, q ^ U.card * w q (familyIndicator D) U) ≤ 1 := by
  apply global_weight_bound q hq0 hq1 (familyIndicator D)
  intro x
  rw [familyIndicator_sq]
  exact familyIndicator_le_one D x

end TalagrandDiscreteConvexity

end

end OAI
