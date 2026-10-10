import Mathlib

namespace OAI

section
namespace ElementaryPositivity
open scoped BigOperators
variable {I M : Type*} [Fintype I] [DecidableEq I] [CommGroup M]
lemma prod_zpow_eq_zpow_sum {α : Type*} (s : Finset α) (f : α → ℤ) (m : M) :
    (∏ x∈s,m ^ f x)=m ^ ∑ x∈s,f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih => simp only [Finset.prod_insert hx,Finset.sum_insert hx,zpow_add,ih]

lemma inverseEuler_exponent (a : I → I → ℕ) (d e : I → ℕ) :
    (∑ i,∑ j, ((if i=j then 1 else 0)-(a i j:ℤ))*(d i:ℤ)*e j)=
      (∑ i,(d i:ℤ)*e i)-∑ i,∑ j,(a i j:ℤ)*d i*e j := by
  simp only [sub_mul,Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

lemma inverseEuler_unit_product (a : I → I → ℕ) (d e : I → ℕ) (m : M) :
    (∏ i,∏ j,∏ _x : Fin (d i),∏ _y : Fin (e j),
      m ^ ((if i=j then 1 else 0)-(a i j:ℤ)))=
    m ^ ((∑ i,(d i:ℤ)*e i)-∑ i,∑ j,(a i j:ℤ)*d i*e j) := by
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simp only [← zpow_natCast,← zpow_mul,prod_zpow_eq_zpow_sum]
  congr 1
  rw [← inverseEuler_exponent a d e]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring
end ElementaryPositivity

end

end OAI
