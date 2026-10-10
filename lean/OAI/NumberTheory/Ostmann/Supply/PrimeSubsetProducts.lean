import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Finset.Powerset
import OAI.NumberTheory.Ostmann.QuadraticSieve.PublishedQuadraticSieve

namespace OAI

/-! # Products of distinct primes index the amplified coefficient array -/

namespace Ostmann

open scoped BigOperators Classical

def primeSubsetProducts (P : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (P.powersetCard k).image fun Q => ∏ p ∈ Q, p

theorem primeSubset_product_injective (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun Q : Finset ℕ => ∏ p ∈ Q, p) {Q | Q ⊆ P} := by
  intro Q hQ R hR heq
  have h := congrArg Nat.primeFactors heq
  rwa [Nat.primeFactors_prod (fun p hp => hP p (hQ hp)),
    Nat.primeFactors_prod (fun p hp => hP p (hR hp))] at h

theorem primeSubsetProducts_card (P : Finset ℕ) (k : ℕ)
    (hP : ∀ p ∈ P, p.Prime) : (primeSubsetProducts P k).card = P.card.choose k := by
  rw [primeSubsetProducts, Finset.card_image_iff.mpr]
  · exact Finset.card_powersetCard k P
  · intro Q hQ R hR h
    exact primeSubset_product_injective P hP
      (Finset.mem_powersetCard.mp hQ).1 (Finset.mem_powersetCard.mp hR).1 h

theorem primeSubset_product_squarefree (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) : Squarefree (∏ p ∈ Q, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hQ p hp) (hQ q hq)).mpr hpq)
  · intro p hp
    exact (hQ p hp).squarefree

theorem primeSubsetProducts_mem_range (P : Finset ℕ) (k Z : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (hZ : ∀ p ∈ P, p ≤ Z) : primeSubsetProducts P k ⊆ oddSquarefreeRange (Z ^ k) := by
  intro s hs
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨hQP, hcard⟩ := Finset.mem_powersetCard.mp hQ
  have hprime : ∀ p ∈ Q, p.Prime := fun p hp => hP p (hQP hp)
  have hsf := primeSubset_product_squarefree Q hprime
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hsf.ne_zero, ?_⟩, ?_, hsf⟩
  · simpa only [hcard] using Finset.prod_le_pow_card Q (fun p => p) Z (fun p hp => hZ p (hQP hp))
  · have ho : ∀ p ∈ Q, Odd p := fun p hp => hodd p (hQP hp)
    clear hprime hsf hcard hQP hQ hs
    induction Q using Finset.induction_on with
    | empty => simp
    | @insert p Q hp ih =>
      rw [Finset.prod_insert hp]
      exact (ho p (Finset.mem_insert_self _ _)).mul
        (ih (fun q hq => ho q (Finset.mem_insert_of_mem hq)))

end Ostmann

end OAI
