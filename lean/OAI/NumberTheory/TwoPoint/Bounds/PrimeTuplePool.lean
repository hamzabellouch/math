import OAI.NumberTheory.TwoPoint.Bounds.PrimeTupleMass

namespace OAI

/-! Arithmetic support of the actual one-prime-per-band tuple family. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def primeTuplePool {J : ℕ} (P : Fin J → Finset ℕ) : Finset ℕ :=
  univ.biUnion P

lemma mem_primeTuplePool {J : ℕ} {P : Fin J → Finset ℕ} {p : ℕ} :
    p ∈ primeTuplePool P ↔ ∃ j, p ∈ P j := by
  simp only [primeTuplePool, mem_biUnion, mem_univ, true_and]

lemma primeTuplePool_prime {J : ℕ} {P : Fin J → Finset ℕ}
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime) {p : ℕ} (hp : p ∈ primeTuplePool P) :
    p.Prime := by
  obtain ⟨j, hj⟩ := mem_primeTuplePool.mp hp
  exact hprime j p hj

lemma primeHarmonicMass_eq_sum (S : Finset ℕ) :
    primeHarmonicMass S = ∑ p ∈ S, 1 / (p : ℝ) := by
  unfold primeHarmonicMass
  simpa only [one_div] using sum_coe_sort S (fun p : ℕ => 1 / (p : ℝ))

lemma primeHarmonicMass_mono {S T : Finset ℕ} (hST : S ⊆ T) :
    primeHarmonicMass S ≤ primeHarmonicMass T := by
  rw [primeHarmonicMass_eq_sum, primeHarmonicMass_eq_sum]
  exact sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ => by positivity)

lemma primeTuplePool_mass {J : ℕ} (P : Fin J → Finset ℕ)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    primeHarmonicMass (primeTuplePool P) = ∑ j, primeHarmonicMass (P j) := by
  simp only [primeHarmonicMass_eq_sum, primeTuplePool]
  apply sum_biUnion
  intro j _ l _ hne
  exact hdisjoint j l (Ne.symm hne)

lemma primeTupleDivisors_arithmetic {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    {d : ℕ} (hd : d ∈ primeTupleDivisors P) :
    Squarefree d ∧ d.primeFactors.card = J ∧ d.primeFactors ⊆ primeTuplePool P := by
  obtain ⟨x, _, rfl⟩ := mem_image.mp hd
  have hf : (∏ j, (x j).val).primeFactors = univ.image (fun j => (x j).val) :=
    familyTuple_primeFactors (fun j (p : P j) => p.val)
      (fun j p => hprime j _ p.property) x (selectedPrimeValues_injective x hdisjoint)
  refine ⟨?_, ?_, ?_⟩
  · exact columnTuple_squarefree (fun j (_ : Fin 1) => x j) 0 hprime hdisjoint
  · rw [hf, card_image_of_injective _ (selectedPrimeValues_injective x hdisjoint),
      card_univ, Fintype.card_fin]
  · rw [hf]
    intro p hp
    obtain ⟨j, _, rfl⟩ := mem_image.mp hp
    exact mem_primeTuplePool.mpr ⟨j, (x j).property⟩

lemma retainedPrimeDivisor_squarefree (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    {q : ℕ} (hq : q ∈ retainedPrimeDivisors Q) : Squarefree q := by
  obtain ⟨U, hU, rfl⟩ := mem_image.mp hq
  have hprime (p : ℕ) (hp : p ∈ U) := hQ p ((mem_powerset.mp hU) hp)
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp r hr hne
    change IsRelPrime p r
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hprime p hp) (hprime r hr)).mpr hne
  · intro p hp
    exact (hprime p hp).squarefree

noncomputable def boundedPaddingDivisors (Q : Finset ℕ) (M : ℕ) : Finset ℕ :=
  (retainedPrimeDivisors Q).filter (fun q => q.primeFactors.card ≤ M)

noncomputable def primeFamilyPairs {J : ℕ} (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (M : ℕ) (eligible : ℕ → ℕ → Prop) : Finset (ℕ × ℕ) :=
  ((primeTupleDivisors P).product (boundedPaddingDivisors Q M)).filter
    (fun dq => eligible dq.1 dq.2)

lemma mem_primeFamilyPairs {J : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    {M : ℕ} {eligible : ℕ → ℕ → Prop} {dq : ℕ × ℕ} :
    dq ∈ primeFamilyPairs P Q M eligible ↔
      dq.1 ∈ primeTupleDivisors P ∧ dq.2 ∈ retainedPrimeDivisors Q ∧
        dq.2.primeFactors.card ≤ M ∧ eligible dq.1 dq.2 := by
  rcases dq with ⟨d, q⟩
  simp only [primeFamilyPairs, boundedPaddingDivisors, Finset.product_eq_sprod,
    mem_filter, Finset.mem_product]
  tauto

end TwoPointCorrelations

end OAI
