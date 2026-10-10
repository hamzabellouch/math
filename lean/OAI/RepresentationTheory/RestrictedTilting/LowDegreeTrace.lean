import Mathlib

namespace OAI

namespace FiberFunctorProof
open scoped BigOperators
universe u v
variable {k : Type u} [Field k] {E : Type v} [AddGroup E] [Fintype E] [DecidableEq E]

 

lemma additive_lagrange_denominator (l : E →+ k) (a : E) :
    (∏ b ∈ Finset.univ.erase a, (l a - l b)) =
      ∏ b ∈ Finset.univ.erase 0, l b := by
  classical
  apply Finset.prod_equiv (Equiv.subLeft a)
  · intro b
    simp [Equiv.subLeft_apply, sub_eq_zero, eq_comm]
  · intro b _
    simp

 

theorem finite_additive_polynomial_sum_zero (l : E →+ k) (hl : Function.Injective l)
    (P : Polynomial k) (hP : P.natDegree < Fintype.card E - 1) :
    ∑ a : E, P.eval (l a) = 0 := by
  classical
  let c : k := ∏ b ∈ Finset.univ.erase (0 : E), l b
  have hc : c ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha hz
    have h := hl (show l a = l 0 by simpa using hz)
    exact (Finset.mem_erase.mp ha).1 h
  have hd : P.degree < (Finset.univ : Finset E).card := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast (show P.natDegree < Fintype.card E by omega)
  have he := Lagrange.coeff_eq_sum (s := Finset.univ) (v := l) hl.injOn hd
  have hcoe : P.coeff ((Finset.univ : Finset E).card - 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hP)
  rw [hcoe] at he
  simp only [additive_lagrange_denominator, ← Finset.sum_div] at he
  exact (div_eq_zero_iff.mp he.symm).resolve_right hc

lemma finite_additive_power_sum_zero (l : E →+ k) (hl : Function.Injective l)
    (n : ℕ) (hn : n < Fintype.card E - 1) : ∑ a : E, l a ^ n = 0 := by
  simpa using finite_additive_polynomial_sum_zero l hl (Polynomial.X ^ n) (by simpa using hn)
end FiberFunctorProof

end OAI
