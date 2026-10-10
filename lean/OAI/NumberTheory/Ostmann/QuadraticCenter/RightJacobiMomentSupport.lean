import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiIncidence

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

def primeSubsetProduct {P : Finset ℕ} (s : Finset P) : ℕ := ∏ p ∈ s, p.val

theorem primeSubsetProduct_eq_image_prod {P : Finset ℕ} (s : Finset P) :
    primeSubsetProduct s = ∏ p ∈ s.image Subtype.val, p := by
  classical
  rw [Finset.prod_image]
  · rfl
  · exact fun a _ b _ h => Subtype.ext h

theorem primeSubsetProduct_squarefree {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (s : Finset P) : Squarefree (primeSubsetProduct s) := by
  classical
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro a ha b hb hab
    apply Nat.coprime_iff_isRelPrime.mp
    exact (Nat.coprime_primes (hP a.val a.property) (hP b.val b.property)).mpr
      (fun h => hab (Subtype.ext h))
  · intro p hp
    exact (hP p.val p.property).squarefree

theorem primeSubsetProduct_primeFactors {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (s : Finset P) :
    (primeSubsetProduct s).primeFactors = s.image Subtype.val := by
  rw [primeSubsetProduct_eq_image_prod]
  apply Nat.primeFactors_prod
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  exact hP q.val q.property

theorem primeSubsetProduct_primeFactors_subset {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (s : Finset P) :
    (primeSubsetProduct s).primeFactors ⊆ P := by
  rw [primeSubsetProduct_primeFactors hP]
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  exact q.property

@[simp] theorem primeSupportWithin_primeSubsetProduct {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (s : Finset P) :
    primeSupportWithin P (primeSubsetProduct s) = s := by
  classical
  ext p
  rw [mem_primeSupportWithin, primeSubsetProduct_primeFactors hP]
  simp only [Finset.mem_image, Subtype.val_inj, exists_eq_right]

end Ostmann.QuadraticCenter

end OAI
