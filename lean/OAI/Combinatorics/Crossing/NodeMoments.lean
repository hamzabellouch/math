import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section
namespace Zarankiewicz
open Polynomial
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def nodePolynomial (node : ι → ℝ) : ℝ[X] := ∏ i, (X-C (node i))

def derivativeAtNode (node : ι → ℝ) (i : ι) : ℝ :=
  (nodePolynomial node).derivative.eval (node i)

theorem derivativeAtNode_eq_prod (node : ι → ℝ) (i : ι) :
    derivativeAtNode node i = ∏ j ∈ Finset.univ.erase i, (node i-node j) := by
  unfold derivativeAtNode nodePolynomial
  change (Lagrange.nodal Finset.univ node).derivative.eval (node i) = _
  rw [Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i), Lagrange.eval_nodal]

theorem derivativeAtNode_ne_zero (node : ι → ℝ) (hn : Function.Injective node) (i : ι) :
    derivativeAtNode node i ≠ 0 := by
  rw [derivativeAtNode_eq_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro hij
  exact (Finset.mem_erase.mp hj).1 (hn hij).symm

theorem node_polynomial_moment (node : ι → ℝ) (hn : Function.Injective node)
    (P : ℝ[X]) (hP : P.degree < (Fintype.card ι - 1 : ℕ)) :
    (∑ i, P.eval (node i) / derivativeAtNode node i) = 0 := by
  by_cases hcard : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    simp
  have hp' : P.degree < (Finset.univ : Finset ι).card :=
    hP.trans_le (by exact_mod_cast Nat.sub_le (Fintype.card ι) 1)
  have he := Lagrange.coeff_eq_sum (s := Finset.univ) (v := node) hn.injOn hp'
  rw [Finset.card_univ, coeff_eq_zero_of_degree_lt hP] at he
  simpa only [Finset.card_univ, derivativeAtNode_eq_prod] using he.symm

theorem node_power_moment (node : ι → ℝ) (hn : Function.Injective node)
    (k : ℕ) (hk : k+1 < Fintype.card ι) :
    (∑ i, node i ^ k / derivativeAtNode node i) = 0 := by
  have hdeg : (X^k : ℝ[X]).degree < (Fintype.card ι - 1 : ℕ) := by
    rw [degree_X_pow]
    exact_mod_cast (show k < Fintype.card ι-1 by omega)
  simpa only [eval_pow, eval_X] using node_polynomial_moment node hn (X^k) hdeg

end Zarankiewicz

end

end OAI
