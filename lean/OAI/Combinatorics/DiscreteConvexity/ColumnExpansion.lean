import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic

namespace OAI

/-!
# A product expansion on a prescribed set of coordinates

Only coordinates in `S` contribute correction terms.  Expanding their product
therefore gives a sum indexed by `S.powerset`, with the factors outside `S`
left unchanged.
-/

namespace TalagrandDiscreteConvexity

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem prod_ite_split (S U : Finset V) (P C : V → ℝ) (hU : U ⊆ S) :
    (∏ i, if i ∈ U then C i else P i) =
      ((∏ i ∈ U, C i) * ∏ i ∈ S \ U, P i) * ∏ i ∈ Sᶜ, P i := by
  calc
    (∏ i, if i ∈ U then C i else P i) =
        (∏ i ∈ S, if i ∈ U then C i else P i) *
          ∏ i ∈ Sᶜ, if i ∈ U then C i else P i :=
      (Finset.prod_mul_prod_compl S _).symm
    _ = ((∏ i ∈ U, C i) * ∏ i ∈ S \ U, P i) * ∏ i ∈ Sᶜ, P i := by
      congr 1
      · simpa only [Finset.piecewise, Finset.inter_eq_right.mpr hU] using
          Finset.prod_piecewise S U C P
      · apply Finset.prod_congr rfl
        intro i hi
        have hiU : i ∉ U := fun h => (Finset.mem_compl.mp hi) (hU h)
        simp only [ite_eq_right hiU]

/-- Expand a product with correction terms restricted to `S`. -/
theorem prod_sub_ite_eq_sum_powerset (S : Finset V) (P C : V → ℝ) :
    (∏ i, (P i - if i ∈ S then C i else 0)) =
      ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * ∏ i, if i ∈ U then C i else P i := by
  have hsplit :
      (∏ i, (P i - if i ∈ S then C i else 0)) =
        (∏ i ∈ S, (P i - C i)) * ∏ i ∈ Sᶜ, P i := by
    calc
      (∏ i, (P i - if i ∈ S then C i else 0)) =
          (∏ i ∈ S, (P i - if i ∈ S then C i else 0)) *
            ∏ i ∈ Sᶜ, (P i - if i ∈ S then C i else 0) :=
        (Finset.prod_mul_prod_compl S _).symm
      _ = (∏ i ∈ S, (P i - C i)) * ∏ i ∈ Sᶜ, P i := by
        congr 1
        · apply Finset.prod_congr rfl
          intro i hi
          simp only [ite_eq_left hi]
        · apply Finset.prod_congr rfl
          intro i hi
          simp only [ite_eq_right (Finset.mem_compl.mp hi), sub_zero]
  rw [hsplit, Finset.prod_sub, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro U hU
  rw [prod_ite_split S U P C (Finset.mem_powerset.mp hU)]
  simp only [mul_assoc]
  rw [mul_left_comm (∏ i ∈ S \ U, P i) (∏ i ∈ U, C i)]

end TalagrandDiscreteConvexity

end OAI
