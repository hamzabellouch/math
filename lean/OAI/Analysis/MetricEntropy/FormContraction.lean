import OAI.Analysis.MetricEntropy.SymmetricForms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

namespace OAI

universe uK

/-!
# Contraction of symmetric forms

The coefficients of a contraction are obtained by summing the original
coefficients against the fixed vector.  Evaluation is literally evaluation of
that original form with the vector in the first slot.  The proof reindexes all
ordered basis tuples, including repeated indices and the empty remaining tuple.
-/

namespace MetricEntropyDuality
namespace SymmetricForm

open scoped BigOperators

variable {K : Type uK} {r j : ℕ}

section CommSemiring

variable [CommSemiring K]

/-- Fix the first vector of a symmetric form, retaining its multiset coefficients. -/
def contract (v : Fin r → K) (F : SymmetricForm K r (j + 1)) :
    SymmetricForm K r j :=
  fun s => ∑ a : Fin r, v a * F (Sym.cons a s)

@[simp] theorem contract_apply (v : Fin r → K) (F : SymmetricForm K r (j + 1))
    (s : Sym (Fin r) j) :
    contract v F s = ∑ a : Fin r, v a * F (Sym.cons a s) := rfl

@[simp] theorem contract_zero (v : Fin r → K) :
    contract v (0 : SymmetricForm K r (j + 1)) = 0 := by
  funext s
  simp [contract]

@[simp] theorem contract_add (v : Fin r → K) (F G : SymmetricForm K r (j + 1)) :
    contract v (F + G) = contract v F + contract v G := by
  funext s
  simp [contract, mul_add, Finset.sum_add_distrib]

@[simp] theorem contract_smul (v : Fin r → K) (c : K)
    (F : SymmetricForm K r (j + 1)) :
    contract v (c • F) = c • contract v F := by
  funext s
  change (∑ a : Fin r, v a * (c * F (Sym.cons a s))) =
    c * ∑ a : Fin r, v a * F (Sym.cons a s)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ac_rfl

/-- The actual contraction map used as a partition label. -/
def contractLinearMap (v : Fin r → K) :
    SymmetricForm K r (j + 1) →ₗ[K] SymmetricForm K r j where
  toFun := contract v
  map_add' := contract_add v
  map_smul' := contract_smul v

@[simp] theorem contractLinearMap_apply (v : Fin r → K)
    (F : SymmetricForm K r (j + 1)) : contractLinearMap v F = contract v F := rfl

/-- Coefficient contraction agrees with inserting the fixed vector into evaluation. -/
theorem eval_contract (v : Fin r → K) (F : SymmetricForm K r (j + 1))
    (args : Fin j → (Fin r → K)) :
    eval (contract v F) args = eval F (Fin.cons v args) := by
  classical
  have hsplit : eval F (Fin.cons v args) =
      ∑ b : Fin r, ∑ a : Fin j → Fin r,
        F (Sym.cons b (tupleSym a)) * (v b * ∏ i, args i (a i)) := by
    unfold eval
    rw [← (Fin.consEquiv (fun _ : Fin (j + 1) => Fin r)).sum_comp
      (fun a : Fin (j + 1) → Fin r => F (tupleSym a) *
        ∏ i : Fin (j + 1), (Fin.cons v args : Fin (j + 1) → (Fin r → K)) i (a i))]
    rw [Fintype.sum_prod_type]
    change (∑ b : Fin r, ∑ a : Fin j → Fin r,
      F (tupleSym (Fin.cons b a)) *
        ∏ i : Fin (j + 1), (Fin.cons v args : Fin (j + 1) → (Fin r → K)) i
          ((Fin.cons b a : Fin (j + 1) → Fin r) i)) = _
    simp only [tupleSym_cons, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [hsplit]
  change (∑ a : Fin j → Fin r,
    (∑ b : Fin r, v b * F (Sym.cons b (tupleSym a))) * ∏ i, args i (a i)) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ac_rfl

end CommSemiring

section CommRing

variable [CommRing K]

@[simp] theorem contract_sub (v : Fin r → K) (F G : SymmetricForm K r (j + 1)) :
    contract v (F - G) = contract v F - contract v G :=
  (contractLinearMap v).map_sub F G

end CommRing

end SymmetricForm
end MetricEntropyDuality

end OAI
