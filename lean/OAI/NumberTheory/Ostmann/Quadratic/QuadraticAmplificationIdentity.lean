import OAI.NumberTheory.Ostmann.Quadratic.QuadraticAmplificationCoefficients
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveTranspose
import OAI.NumberTheory.Ostmann.Construction.DistinctProductError

namespace OAI

/-! # Identifying the shared coefficient test with the distinct-prime expansion -/

namespace Ostmann

open scoped BigOperators Classical

theorem jacobi_product_right (u : ℤ) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p ≠ 0) :
    jacobiSym u (∏ p ∈ Q, p) = ∏ p ∈ Q, jacobiSym u p := by
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert p Q hp ih =>
    have hpn := hQ p (Finset.mem_insert_self _ _)
    have hQn : ∀ q ∈ Q, q ≠ 0 := fun q hq => hQ q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hp, jacobiSym.mul_right' u hpn
      (Finset.prod_ne_zero_iff.mpr hQn), ih hQn, Finset.prod_insert hp]

theorem subset_product_sum_subtype (P : Finset ℕ) (k : ℕ) (y : ℕ → ℂ) :
    (∑ Q ∈ (Finset.univ : Finset P).powersetCard k, ∏ p ∈ Q, y p) =
      ∑ Q ∈ P.powersetCard k, ∏ p ∈ Q, y p := by
  let f : P ↪ ℕ := Function.Embedding.subtype _
  have hmap : (Finset.univ : Finset P).map f = P := by ext p; simp [f]
  have h := congrArg (fun R : Finset ℕ => ∑ Q ∈ R.powersetCard k, ∏ p ∈ Q, y p) hmap
  simp only [Finset.powersetCard_map, Finset.sum_map] at h
  change (∑ Q ∈ (Finset.univ : Finset P).powersetCard k, ∏ p ∈ Q.map f, y p) = _ at h
  simpa [f] using h

theorem quadratic_amplification_identity (P : Finset ℕ) (k Z : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p) (hZ : ∀ p ∈ P, p ≤ Z)
    (c : ℂ) (e : ℕ → ℂ) (u : ℤ) :
    quadraticTransposeSum (Z ^ k) (primeSubsetCoefficient P k c e) u =
      c * ∑ Q ∈ P.powersetCard k, ∏ p ∈ Q, e p * (jacobiSym u p : ℂ) := by
  let f : ℕ → ℂ := fun s => primeSubsetCoefficient P k c e s * (jacobiSym u s : ℂ)
  have hsub := primeSubsetProducts_mem_range P k Z hP hodd hZ
  have hs : (∑ s ∈ primeSubsetProducts P k, f s) =
      ∑ s ∈ oddSquarefreeRange (Z ^ k), f s := by
    apply Finset.sum_subset hsub
    intro s _ hs
    simp [f, primeSubsetCoefficient, hs]
  change (∑ s ∈ oddSquarefreeRange (Z ^ k), f s) = _
  rw [← hs]
  unfold primeSubsetProducts
  rw [Finset.sum_image, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro Q hQ
    have hQP := (Finset.mem_powersetCard.mp hQ).1
    have hprime : ∀ p ∈ Q, p.Prime := fun p hp => hP p (hQP hp)
    have hmem : (∏ p ∈ Q, p) ∈ primeSubsetProducts P k :=
      Finset.mem_image.mpr ⟨Q, hQ, rfl⟩
    dsimp only [f]
    simp only [primeSubsetCoefficient, hmem, ite_true]
    rw [Nat.primeFactors_prod hprime,
      jacobi_product_right u Q (fun p hp => (hprime p hp).ne_zero), Int.cast_prod,
      Finset.prod_mul_distrib, mul_assoc]
  · intro Q hQ R hR heq
    exact primeSubset_product_injective P hP
      (Finset.mem_powersetCard.mp hQ).1 (Finset.mem_powersetCard.mp hR).1 heq

end Ostmann

end OAI
