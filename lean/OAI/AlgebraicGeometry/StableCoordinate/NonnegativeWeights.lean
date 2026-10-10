import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic

namespace OAI

/-!
# Nonnegative polynomial weights

The final step of the source rigidity argument uses the weights `(1, 1, 0)`
on the algebraically independent generators `a, d, u`.  This module proves
that the resulting polynomial algebra has no nonzero homogeneous elements
of negative weight.  It does not assume or assert the geometric interfaces
needed to identify this polynomial algebra inside the source quotient.
-/

namespace StableCoordinate

open MvPolynomial

section General

variable {σ K : Type*} [CommSemiring K]

/-- A monomial has nonnegative integral weight when all variable weights are
nonnegative.  Variables of weight zero are allowed. -/
theorem monomial_weight_nonneg (w : σ → ℤ) (hw : ∀ i, 0 ≤ w i)
    (d : σ →₀ ℕ) : 0 ≤ Finsupp.weight w d := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_nonneg fun i _ => nsmul_nonneg (hw i) (d i)

/-- Every nonzero homogeneous polynomial for nonnegative variable weights
has nonnegative weight. -/
theorem homogeneous_weight_nonneg {w : σ → ℤ} (hw : ∀ i, 0 ≤ w i)
    {p : MvPolynomial σ K} (hp : p ≠ 0) {n : ℤ}
    (hn : p.IsWeightedHomogeneous w n) : 0 ≤ n := by
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hp
  rw [← hn hd]
  exact monomial_weight_nonneg w hw d

/-- No polynomial supported on nonnegative variable weights can be nonzero
and homogeneous of negative weight. -/
theorem eq_zero_of_homogeneous_negative {w : σ → ℤ} (hw : ∀ i, 0 ≤ w i)
    {p : MvPolynomial σ K} {n : ℤ}
    (hn : p.IsWeightedHomogeneous w n) (hneg : n < 0) : p = 0 := by
  by_contra hp
  exact (not_le_of_gt hneg) (homogeneous_weight_nonneg hw hp hn)

/-- The negative homogeneous components all vanish. -/
theorem homogeneousComponent_negative {w : σ → ℤ} (hw : ∀ i, 0 ≤ w i)
    (p : MvPolynomial σ K) {n : ℤ} (hneg : n < 0) :
    MvPolynomial.weightedHomogeneousComponent w n p = 0 := by
  apply eq_zero_of_homogeneous_negative hw
  · exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous n p
  · exact hneg

end General

/-- The weights of the source polynomial subalgebra `k[a,d,u]`: index `0`
is `a`, index `1` is `d`, and index `2` is `u`. -/
def rigidityPolynomialWeight (i : Fin 3) : ℤ := if i = 2 then 0 else 1

theorem rigidityPolynomialWeight_nonneg (i : Fin 3) :
    0 ≤ rigidityPolynomialWeight i := by
  unfold rigidityPolynomialWeight
  split_ifs <;> norm_num

/-- The precise impossibility used for the coefficient `q` in source
§5: a polynomial in `a,d,u` of fiber weight `-2` must vanish. -/
theorem rigidity_polynomial_weight_neg_two {K : Type*} [CommSemiring K]
    {q : MvPolynomial (Fin 3) K}
    (hq : q.IsWeightedHomogeneous rigidityPolynomialWeight (-2)) : q = 0 := by
  exact eq_zero_of_homogeneous_negative rigidityPolynomialWeight_nonneg hq (by norm_num)

/-- Contradiction form for the final source rigidity step. -/
theorem no_nonzero_rigidity_polynomial_weight_neg_two {K : Type*} [CommSemiring K]
    (q : MvPolynomial (Fin 3) K) (hq : q ≠ 0) :
    ¬ q.IsWeightedHomogeneous rigidityPolynomialWeight (-2) := by
  intro hweight
  exact hq (rigidity_polynomial_weight_neg_two hweight)

end StableCoordinate

end OAI
