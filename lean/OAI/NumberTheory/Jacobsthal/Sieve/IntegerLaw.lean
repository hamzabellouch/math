import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.SmoothNumbers
import OAI.NumberTheory.Jacobsthal.Estimates.ProductRestriction

namespace OAI

namespace Erdos970


namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

def integerProduct (E : Finset ℕ) (k : E → ℕ) : ℕ := ∏ p : E, (p : ℕ) ^ k p

variable (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p)
include hE

lemma integerProduct_pos (k : E → ℕ) : 0 < integerProduct E k := by
  exact Finset.prod_pos (fun p _ => pow_pos (hE p p.property).pos _)

theorem integerProduct_factorization (k : E → ℕ) (q : E) :
    (integerProduct E k).factorization q = k q := by
  classical
  rw [integerProduct, Nat.factorization_prod (S := Finset.univ) (g := fun p : E => (p : ℕ) ^ k p) (fun p _ => pow_ne_zero _ (hE p p.property).ne_zero)]
  simp only [Finsupp.finsetSum_apply]
  have h (p : E) : ((p : ℕ) ^ k p).factorization q = if p = q then k p else 0 := by
    rw [(hE p p.property).factorization_pow]
    simp only [Finsupp.single_apply, Subtype.val_inj]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem integerProduct_injective : Function.Injective (integerProduct E) := by
  intro a b hab
  funext p
  simpa only [integerProduct_factorization E hE] using congrArg (fun d : ℕ => d.factorization p) hab

theorem integerProduct_factorization_outside (k : E → ℕ) {q : ℕ} (hq : q ∉ E) :
    (integerProduct E k).factorization q = 0 := by
  rw [integerProduct, Nat.factorization_prod (S := Finset.univ)
    (g := fun p : E => (p : ℕ) ^ k p) (fun p _ => pow_ne_zero _ (hE p p.property).ne_zero)]
  simp only [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro p _
  rw [(hE p p.property).factorization_pow]
  apply Finsupp.single_eq_of_ne
  intro hpq
  exact hq (hpq ▸ p.property)

theorem integerProduct_support (k : E → ℕ) : (integerProduct E k).primeFactors ⊆ E := by
  intro q hq
  by_contra hn
  have hh : q ∈ (integerProduct E k).factorization.support := by
    simpa only [Nat.support_factorization] using hq
  exact Finsupp.mem_support_iff.mp hh (integerProduct_factorization_outside E hE k hn)

omit hE in

theorem integerProduct_factorization_reconstruct {d : ℕ} (hd : d ≠ 0)
    (hs : d.primeFactors ⊆ E) :
    integerProduct E (fun p => d.factorization p) = d := by
  rw [integerProduct]
  change (∏ p ∈ E.attach, (p : ℕ) ^ d.factorization p) = d
  rw [Finset.prod_attach E (fun p : ℕ => p ^ d.factorization p)]
  calc
    _ = d.factorization.prod (· ^ ·) := by
      symm
      apply Finset.prod_subset
      · simpa only [Nat.support_factorization] using hs
      · intro p _ hp
        have hz : d.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
        simp only [hz, pow_zero]
    _ = d := Nat.prod_factorization_pow_eq_self hd

end EulerWeightedLower


end Erdos970

end OAI
