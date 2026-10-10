import OAI.NumberTheory.Ostmann.Supply.PrimeSubsetMainTerm
import OAI.NumberTheory.Ostmann.Preliminaries.BoundedSieveSubsets
import OAI.NumberTheory.Ostmann.Preliminaries.AdditiveSieveProof

namespace OAI

/-! # The support sieve indexed by actual finite sets of primes -/

namespace Ostmann

open scoped Classical BigOperators

 theorem prime_set_support_sieve {M Q : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (S : ∀ p : ℕ, Finset (ZMod p))
    (hS : ∀ p ∈ P, (S p).Nonempty) (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (A : Finset (Fin M)) (hA : A.Nonempty) (J : ℤ)
    (ha : ∀ x ∈ A, ∀ p ∈ P, ((J + (x.val : ℤ) : ℤ) : ZMod p) ∈ S p) :
    (∑ U ∈ boundedSieveSubsets P Q, ∏ p ∈ U, ((p : ℝ) / (S p).card - 1)) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  let e : Fin P.card ≃ P := by
    simpa only [Fintype.card_coe] using (Fintype.equivFin P).symm
  let p : Fin P.card → ℕ := fun i => (e i).val
  have hinj : Function.Injective p := fun i j hij => e.injective (Subtype.ext hij)
  have hmem (i : Fin P.card) : p i ∈ P := (e i).property
  have hcover : ∀ q ∈ P, ∃ i : Fin P.card, p i = q := by
    intro q hq
    refine ⟨e.symm ⟨q, hq⟩, ?_⟩
    simp only [p, Equiv.apply_symm_apply]
  let : ∀ i, Fact (p i).Prime := fun i => ⟨hP _ (hmem i)⟩
  have hc : Pairwise (fun i j => (p i).Coprime (p j)) := by
    intro i j hij
    exact (Nat.coprime_primes (hP _ (hmem i)) (hP _ (hmem j))).mpr
      (fun he => hij (hinj he))
  let G := (Finset.univ : Finset (Fin P.card)).powerset.filter
    (fun R => (∏ i ∈ R, p i) ≤ Q)
  have hGprod : ∀ R ∈ G, (∏ i ∈ R, p i) ≤ Q := fun _ hR => (Finset.mem_filter.mp hR).2
  have hbound := prime_subset_main_term publishedAdditiveLargeSieve p hc (fun i => S (p i))
    (fun i => hS _ (hmem i)) G hQ hM A hA J hGprod
    (fun _ _ x hx i _ => ha x hx (p i) (hmem i))
  have hsum : (∑ R ∈ G, ∏ i ∈ R, ((p i : ℝ) / (S (p i)).card - 1)) =
      ∑ U ∈ boundedSieveSubsets P Q, ∏ q ∈ U, ((q : ℝ) / (S q).card - 1) := by
    apply Finset.sum_bij (fun R _ => R.image p)
    · intro R hR
      have hprod : (∏ q ∈ R.image p, q) = ∏ i ∈ R, p i := by
        rw [Finset.prod_image]; exact fun _ _ _ _ he => hinj he
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · intro q hq
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
        exact hmem i
      · rw [hprod]
        exact hGprod R hR
    · intro R _ T _ he
      exact Finset.image_injective hinj he
    · intro U hU
      have hUP := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
      let R := (Finset.univ : Finset (Fin P.card)).filter fun i => p i ∈ U
      have himage : R.image p = U := by
        ext q
        constructor
        · intro hq
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
          exact (Finset.mem_filter.mp hi).2
        · intro hq
          obtain ⟨i, hi⟩ := hcover q (hUP hq)
          exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, by simpa only [hi] using hq⟩, hi⟩
      refine ⟨R, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩, himage⟩
      have he : (∏ q ∈ U, q) = ∏ i ∈ R, p i := by
        rw [← himage, Finset.prod_image]; exact fun _ _ _ _ hij => hinj hij
      rw [← he]
      exact (Finset.mem_filter.mp hU).2
    · intro R _
      rw [Finset.prod_image]; exact fun _ _ _ _ he => hinj he
  rwa [hsum] at hbound

end Ostmann

end OAI
