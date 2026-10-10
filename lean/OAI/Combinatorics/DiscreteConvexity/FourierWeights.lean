import OAI.Combinatorics.DiscreteConvexity.Bernoulli
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace OAI

noncomputable section
open scoped BigOperators

namespace TalagrandDiscreteConvexity

/-- The alternating factor for a coordinate inside the differentiated set. -/
def correction (q : ℝ) (bit : Bool) : ℝ :=
  if bit then -(1 - q) else 1 - q

@[simp] theorem correction_false (q : ℝ) : correction q false = 1 - q := rfl

@[simp] theorem correction_true (q : ℝ) : correction q true = -(1 - q) := rfl

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Coordinate product defining the alternating partial expectation. -/
def rowKernel (q : ℝ) (U : Finset V) (x : V → Bool) : ℝ :=
  ∏ i, if i ∈ U then correction q (x i) else bitWeight q (x i)

/-- Exactly `(1-q)^|U|` times the alternating sum over the coordinates in `U`,
with independent Bernoulli expectation on its complement. -/
def b (q : ℝ) (f : (V → Bool) → ℝ) (U : Finset V) : ℝ :=
  ∑ x, f x * rowKernel q U x

/-- The nonnegative weights used by both global and exceptional-set bounds. -/
def w (q : ℝ) (f : (V → Bool) → ℝ) (U : Finset V) : ℝ :=
  (b q f U) ^ 2

/-- Separate the alternating coordinates from the independent outside mass. -/
theorem rowKernel_eq_alternating_product (q : ℝ) (U : Finset V) (x : V → Bool) :
    rowKernel q U x = (1 - q) ^ U.card *
      (∏ i ∈ U, if x i then (-1 : ℝ) else 1) *
      ∏ i ∈ Finset.univ \ U, bitWeight q (x i) := by
  have hsplit : rowKernel q U x =
      (∏ i ∈ U, correction q (x i)) *
        ∏ i ∈ Finset.univ \ U, bitWeight q (x i) := by
    simpa only [rowKernel, Finset.piecewise, Finset.univ_inter] using
      (Finset.prod_piecewise Finset.univ U
        (fun i => correction q (x i)) (fun i => bitWeight q (x i)))
  have hc : (∏ i ∈ U, correction q (x i)) =
      (1 - q) ^ U.card * ∏ i ∈ U, if x i then (-1 : ℝ) else 1 := by
    calc
      (∏ i ∈ U, correction q (x i)) =
          ∏ i ∈ U, (1 - q) * (if x i then (-1 : ℝ) else 1) := by
        apply Finset.prod_congr rfl
        intro i _
        cases x i <;> simp [correction]
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [hsplit, hc]

/-- The explicit alternating partial-expectation formula for the coefficient. -/
theorem b_eq_alternating_sum (q : ℝ) (f : (V → Bool) → ℝ) (U : Finset V) :
    b q f U = (1 - q) ^ U.card *
      ∑ x, f x * (∏ i ∈ U, if x i then (-1 : ℝ) else 1) *
        ∏ i ∈ Finset.univ \ U, bitWeight q (x i) := by
  simp only [b, rowKernel_eq_alternating_product, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ac_rfl

@[simp] theorem rowKernel_empty (q : ℝ) (x : V → Bool) :
    rowKernel q ∅ x = cubeWeight q x := by
  simp [rowKernel, cubeWeight]

/-- The empty coefficient is the original biased expectation. -/
@[simp] theorem b_empty (q : ℝ) (f : (V → Bool) → ℝ) :
    b q f ∅ = cubeExpectation q f := by
  simp only [b, rowKernel_empty, cubeExpectation]
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _

theorem w_nonneg (q : ℝ) (f : (V → Bool) → ℝ) (U : Finset V) :
    0 ≤ w q f U := sq_nonneg _

end TalagrandDiscreteConvexity

end

end OAI
