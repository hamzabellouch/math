import OAI.Combinatorics.DiscreteConvexity.Basic
import OAI.Combinatorics.DiscreteConvexity.FourierWeights
import OAI.Combinatorics.DiscreteConvexity.ColumnExpansion
import OAI.Combinatorics.DiscreteConvexity.ExceptionalWeightBound

namespace OAI

/-!
# Signed arrays force weight on every exceptional set

The arrays have one common set of rows. Each column in `S` receives the
Bernoulli product mass minus the product of the alternating corrections.
All-zero columns in `S` have zero signed mass. This gives pointwise vanishing
for exceptional sets, without any nonnegativity assumption on these masses.
Expanding the column products and summing independently over the rows gives
the exact signed coefficient identity.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandDiscreteConvexity

variable {V : Type*} [Fintype V] [DecidableEq V]

def signedArrayMass (q : ℝ) {k : ℕ} (S : Finset V)
    (X : Fin k → V → Bool) : ℝ :=
  ∏ i, ((∏ j, bitWeight q (X j i)) -
    if i ∈ S then ∏ j, correction q (X j i) else 0)

/-- Choosing the correction columns factors into the same coefficient kernel
in every row. -/
theorem columnKernel_eq_rowKernel (q : ℝ) {k : ℕ} (U : Finset V)
    (X : Fin k → V → Bool) :
    (∏ i, if i ∈ U then ∏ j, correction q (X j i)
      else ∏ j, bitWeight q (X j i)) =
      ∏ j, rowKernel q U (X j) := by
  unfold rowKernel
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ U <;> simp only [hi, ite_true, ite_false]

/-- The finite product expansion, followed by exact row factorization.
It is valid for every real q and every real-valued row function. -/
theorem signed_array_identity (q : ℝ) (k : ℕ)
    (f : (V → Bool) → ℝ) (S : Finset V) :
    (∑ X : Fin k → V → Bool, (∏ j, f (X j)) * signedArrayMass q S X) =
      ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * b q f U ^ k := by
  classical
  calc
    (∑ X : Fin k → V → Bool, (∏ j, f (X j)) * signedArrayMass q S X) =
        ∑ X : Fin k → V → Bool, ∑ U ∈ S.powerset,
          (-1 : ℝ) ^ U.card * ∏ j, (f (X j) * rowKernel q U (X j)) := by
      apply Finset.sum_congr rfl
      intro X _
      rw [signedArrayMass, prod_sub_ite_eq_sum_powerset, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U _
      rw [columnKernel_eq_rowKernel, Finset.prod_mul_distrib]
      exact mul_left_comm _ _ _
    _ = ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card *
        ∑ X : Fin k → V → Bool, ∏ j, (f (X j) * rowKernel q U (X j)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro U _
      rw [Finset.mul_sum]
    _ = ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * b q f U ^ k := by
      apply Finset.sum_congr rfl
      intro U _
      congr 1
      rw [← Fintype.prod_sum (fun (_ : Fin k) (x : V → Bool) =>
        f x * rowKernel q U x)]
      simp only [b, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- An all-zero column in S cancels exactly; the masses may be signed. -/
theorem signedArrayMass_eq_zero_of_zero_column (q : ℝ) {k : ℕ}
    {S : Finset V} {X : Fin k → V → Bool} {i : V}
    (hi : i ∈ S) (hzero : ∀ j, X j i = false) :
    signedArrayMass q S X = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi, hzero, bitWeight, correction]

/-- On an exceptional set, either one row leaves the family or some column
of S is all zero. In either case the signed summand vanishes. -/
theorem exceptional_signed_summand_eq_zero (q : ℝ) {k : ℕ}
    {D : Family V} {S : Finset V} (hS : S ∈ exceptional k D)
    (X : Fin k → V → Bool) :
    (∏ j, familyIndicator D (X j)) * signedArrayMass q S X = 0 := by
  classical
  by_cases hrows : ∀ j, cubeSet (X j) ∈ D
  · obtain ⟨i, hi, hmissing⟩ :=
      exceptional_tuple_misses hS (fun j => cubeSet (X j)) hrows
    have hzero (j : Fin k) : X j i = false := by
      cases hbit : X j i with
      | false => rfl
      | true =>
        exact False.elim (hmissing j (by simp [cubeSet, hbit]))
    rw [signedArrayMass_eq_zero_of_zero_column q hi hzero, mul_zero]
  · obtain ⟨j, hj⟩ := not_forall.mp hrows
    have hprod : (∏ j, familyIndicator D (X j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp only [familyIndicator, ite_eq_right hj]
    rw [hprod, zero_mul]

/-- The exact vanishing signed expansion on an exceptional set. -/
theorem exceptional_signed_sum_eq_zero (q : ℝ) {k : ℕ}
    {D : Family V} {S : Finset V} (hS : S ∈ exceptional k D) :
    (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * b q (familyIndicator D) U ^ k) = 0 := by
  rw [← signed_array_identity]
  apply Finset.sum_eq_zero
  intro X _
  exact exceptional_signed_summand_eq_zero q hS X

theorem exceptional_signed_identity (q : ℝ)
    {D : Family V} {S : Finset V} (hS : S ∈ exceptional 32 D) :
    0 = ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * b q (familyIndicator D) U ^ 32 :=
  (exceptional_signed_sum_eq_zero q hS).symm

/-- The actual exceptional-weight bound, at the original family density. -/
theorem exceptional_weight_lower_bound (q : ℝ)
    {D : Family V} (hD : (1 / 2 : ℝ) ≤ familyMeasure q D)
    {S : Finset V} (hS : S ∈ exceptional 32 D) :
    (1 / 2 : ℝ) ^ 32 ≤
      ∑ U ∈ S.powerset.erase ∅, w q (familyIndicator D) U ^ 16 := by
  apply exceptional_lower_bound_of_signed_sum S (b q (familyIndicator D))
    (exceptional_signed_sum_eq_zero q hS)
  simpa only [b_empty, cubeExpectation_familyIndicator] using hD

/-- The filter form used to combine the exceptional bound with weight bins. -/
theorem exceptional_weight_lower_bound_filter (q : ℝ)
    {D : Family V} (hD : (1 / 2 : ℝ) ≤ familyMeasure q D)
    {S : Finset V} (hS : S ∈ exceptional 32 D) :
    (1 / 2 : ℝ) ^ 32 ≤
      ∑ U ∈ S.powerset.filter (fun U => U ≠ ∅), w q (familyIndicator D) U ^ 16 := by
  simpa only [Finset.filter_ne'] using exceptional_weight_lower_bound q hD hS

end TalagrandDiscreteConvexity

end

end OAI
