import OAI.NumberTheory.Ostmann.Characters.SparsePrimeFamilyCard

namespace OAI

/-! # The indexed prime coordinates of a finite selected set -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def primeFamilyEnumeration (P : Finset ℕ) (i : Fin P.card) : ℕ :=
  ((P.equivFin).symm i).val

 theorem primeFamilyEnumeration_mem (P : Finset ℕ) (i : Fin P.card) :
    primeFamilyEnumeration P i ∈ P := ((P.equivFin).symm i).property

 theorem primeFamilyEnumeration_injective (P : Finset ℕ) :
    Function.Injective (primeFamilyEnumeration P) := by
  intro i j hij
  apply (P.equivFin.symm).injective
  exact Subtype.ext hij

 theorem primeFamilyEnumeration_surjective (P : Finset ℕ) (q : ℕ) (hq : q ∈ P) :
    ∃ i, primeFamilyEnumeration P i = q := by
  refine ⟨P.equivFin ⟨q, hq⟩, ?_⟩
  simp [primeFamilyEnumeration]

 theorem primeFamilyEnumeration_image (P : Finset ℕ) :
    Finset.univ.image (primeFamilyEnumeration P) = P := by
  ext q
  constructor
  · rintro hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact primeFamilyEnumeration_mem P i
  · intro hq
    obtain ⟨i, hi⟩ := primeFamilyEnumeration_surjective P q hq
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩

 theorem primeFamilyEnumeration_sum (P : Finset ℕ) (f : ℕ → ℝ) :
    (∑ i, f (primeFamilyEnumeration P i)) = ∑ q ∈ P, f q := by
  calc
    _ = ∑ q ∈ Finset.univ.image (primeFamilyEnumeration P), f q := by
      rw [Finset.sum_image]
      exact fun i _ j _ hij => primeFamilyEnumeration_injective P hij
    _ = _ := by rw [primeFamilyEnumeration_image P]

theorem primeFamilyEnumeration_prod (P : Finset ℕ) :
    (∏ i, primeFamilyEnumeration P i) = ∏ q ∈ P, q := by
  calc
    _ = ∏ q ∈ Finset.univ.image (primeFamilyEnumeration P), q := by
      rw [Finset.prod_image]
      exact fun i _ j _ hij => primeFamilyEnumeration_injective P hij
    _ = _ := by rw [primeFamilyEnumeration_image P]

 theorem primeFamilyEnumeration_coprime (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Pairwise (fun i j => (primeFamilyEnumeration P i).Coprime (primeFamilyEnumeration P j)) := by
  intro i j hij
  exact (Nat.coprime_primes (hP _ (primeFamilyEnumeration_mem P i))
    (hP _ (primeFamilyEnumeration_mem P j))).mpr
      (fun h => hij (primeFamilyEnumeration_injective P h))

noncomputable def primeSubfamilyEmbedding (P Q : Finset ℕ) (hQP : Q ⊆ P) :
    Fin Q.card ↪ Fin P.card where
  toFun i := P.equivFin ⟨primeFamilyEnumeration Q i, hQP (primeFamilyEnumeration_mem Q i)⟩
  inj' := by
    intro i j h
    have hh := (P.equivFin).injective h
    have hn : primeFamilyEnumeration Q i = primeFamilyEnumeration Q j :=
      congrArg (fun x : P => x.val) hh
    exact primeFamilyEnumeration_injective Q hn

 theorem primeFamilyEnumeration_subfamily (P Q : Finset ℕ) (hQP : Q ⊆ P) (i : Fin Q.card) :
    primeFamilyEnumeration P (primeSubfamilyEmbedding P Q hQP i) = primeFamilyEnumeration Q i := by
  simp [primeFamilyEnumeration, primeSubfamilyEmbedding]

noncomputable def finitePrimeFamilyEmbedding {m : ℕ} (P : Finset ℕ)
    (p : Fin m → ℕ) (hinj : Function.Injective p) (hmem : ∀ i, p i ∈ P) :
    Fin m ↪ Fin P.card where
  toFun i := P.equivFin ⟨p i, hmem i⟩
  inj' := by
    intro i j hij
    apply hinj
    exact congrArg (fun x : P => x.val) ((P.equivFin).injective hij)

theorem primeFamilyEnumeration_embedding {m : ℕ} (P : Finset ℕ)
    (p : Fin m → ℕ) (hinj : Function.Injective p) (hmem : ∀ i, p i ∈ P) (i : Fin m) :
    primeFamilyEnumeration P (finitePrimeFamilyEmbedding P p hinj hmem i) = p i := by
  change ((P.equivFin).symm (P.equivFin ⟨p i, hmem i⟩)).val = p i
  simp

end Ostmann

end OAI
