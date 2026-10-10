import OAI.NumberTheory.Ostmann.QuadraticCenter.CompositeCenter

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem primeBlock_pairwise_coprime (U : Finset ℕ) (hU : ∀ p ∈ U, Nat.Prime p) :
    Pairwise (fun p q : U => p.val.Coprime q.val) := by
  intro p q hpq
  exact (Nat.coprime_primes (hU p p.property) (hU q q.property)).mpr
    (fun h => hpq (Subtype.ext h))

def primeBlockCenter (U : Finset ℕ) (hU : ∀ p ∈ U, Nat.Prime p) (t : ℕ → ℤ) : ℕ := by
  letI : ∀ p : U, NeZero p.val := fun p => ⟨(hU p p.property).ne_zero⟩
  letI : NeZero (∏ p : U, p.val) := ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => NeZero.ne p.val)⟩
  exact compositeCenter (fun p : U => p.val) (primeBlock_pairwise_coprime U hU) (fun p => t p)

theorem primeBlockCenter_lt (U : Finset ℕ) (hU : ∀ p ∈ U, Nat.Prime p) (t : ℕ → ℤ) :
    primeBlockCenter U hU t < ∏ p ∈ U, p := by
  let : ∀ p : U, NeZero p.val := fun p => ⟨(hU p p.property).ne_zero⟩
  let : NeZero (∏ p : U, p.val) := ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => NeZero.ne p.val)⟩
  have hh := compositeCenter_lt (fun p : U => p.val) (primeBlock_pairwise_coprime U hU) (fun p => t p)
  simpa only [primeBlockCenter, Finset.prod_coe_sort U (fun p : ℕ => p)] using hh

theorem primeBlockCenter_dvd (U : Finset ℕ) (hU : ∀ p ∈ U, Nat.Prime p) (t : ℕ → ℤ)
    (p : ℕ) (hp : p ∈ U) : (p : ℤ) ∣ (primeBlockCenter U hU t : ℤ) - t p := by
  let : ∀ p : U, NeZero p.val := fun p => ⟨(hU p p.property).ne_zero⟩
  let : NeZero (∏ p : U, p.val) := ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => NeZero.ne p.val)⟩
  exact compositeCenter_dvd (fun p : U => p.val) (primeBlock_pairwise_coprime U hU)
    (fun p => t p) ⟨p, hp⟩

theorem primeBlock_translated_product (U : Finset ℕ) (hU : ∀ p ∈ U, Nat.Prime p)
    (t : ℕ → ℤ) (n : ℤ) :
    (∏ p ∈ U, jacobiSym (n - t p) p) =
      jacobiSym (n - primeBlockCenter U hU t) (∏ p ∈ U, p) := by
  let : ∀ p : U, NeZero p.val := fun p => ⟨(hU p p.property).ne_zero⟩
  let : NeZero (∏ p : U, p.val) := ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => NeZero.ne p.val)⟩
  have hh := translated_jacobi_prod_eq_composite (fun p : U => p.val)
    (primeBlock_pairwise_coprime U hU) (fun p => t p) n
  simpa only [primeBlockCenter, Finset.prod_coe_sort U (fun p : ℕ => p),
    Finset.prod_coe_sort U (fun p : ℕ => jacobiSym (n - t p) p)] using hh

theorem primeBlock_oriented_product (U : Finset ℕ) (hU : ∀ p ∈ U, Nat.Prime p)
    (ε t : ℕ → ℤ) (n : ℤ) :
    (∏ p ∈ U, ε p * jacobiSym (n - t p) p) =
      (∏ p ∈ U, ε p) * jacobiSym (n - primeBlockCenter U hU t) (∏ p ∈ U, p) := by
  rw [Finset.prod_mul_distrib, primeBlock_translated_product U hU t n]

end Ostmann.QuadraticCenter

end

end OAI
