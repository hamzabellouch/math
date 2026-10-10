import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseBernoulliFeatures

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n : ℕ}

theorem flag_zero_or_one (q : Fin n → Bool) (i : Fin n) : flag q i=0 ∨ flag q i=1 := by
  unfold flag
  split_ifs <;> simp

theorem flag_mul_self (q : Fin n → Bool) (i : Fin n) : flag q i*flag q i=flag q i := by
  rcases flag_zero_or_one q i with h | h <;> simp [h]

theorem flag_mul_product (q : Fin n → Bool) (S : Finset (Fin n)) (i : Fin n) (hi : i∈S) :
    flag q i*(∏ j∈S,flag q j)=∏ j∈S,flag q j := by
  conv_rhs => rw [← mul_prod_erase S (flag q) hi]
  rw [← mul_prod_erase S (flag q) hi,← mul_assoc,flag_mul_self]

theorem product_union (q : Fin n → Bool) (S T : Finset (Fin n)) :
    (∏ i∈S,flag q i)*(∏ i∈T,flag q i)=∏ i∈S∪T,flag q i := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [prod_insert hi,mul_assoc,ih,insert_union]
    by_cases hit : i∈T
    · have hum : i∈S∪T := mem_union_right S hit
      rw [insert_eq_of_mem hum]
      exact flag_mul_product q _ i hum
    · rw [prod_insert (by simp only [mem_union,not_or]; exact ⟨hi,hit⟩)]

end MetricKMedian.SparseBernoulli

end OAI
