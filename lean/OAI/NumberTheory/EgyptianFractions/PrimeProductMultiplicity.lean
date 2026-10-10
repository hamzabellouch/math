import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- The ordered prime tuples of length `k` whose product is `N`. -/
def primeProductFiber (k N : ℕ) : Set (Fin k → ℕ) :=
  {p | (∀ i, Nat.Prime (p i)) ∧ ∏ i, p i = N}

theorem prime_tuple_perm_factors {k N : ℕ} {p : Fin k → ℕ}
    (hp : p ∈ primeProductFiber k N) :
    (List.ofFn p).Perm N.primeFactorsList := by
  apply Nat.primeFactorsList_unique
  · simpa only [List.prod_ofFn] using hp.2
  · intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    exact hp.1 i

theorem primeProductFiber_finite (k N : ℕ) : (primeProductFiber k N).Finite := by
  classical
  let t : Finset (List ℕ) := N.primeFactorsList.permutations.toFinset
  have hsub : List.ofFn '' primeProductFiber k N ⊆ (t : Set (List ℕ)) := by
    rintro _ ⟨p, hp, rfl⟩
    exact List.mem_toFinset.mpr (List.mem_permutations.mpr (prime_tuple_perm_factors hp))
  exact (t.finite_toSet.subset hsub).of_finite_image List.ofFn_injective.injOn

/-- Unique factorization bounds each atom of an ordered prime product by `k!`. -/
theorem primeProductFiber_ncard_le (k N : ℕ) :
    (primeProductFiber k N).ncard ≤ k.factorial := by
  classical
  by_cases hne : (primeProductFiber k N).Nonempty
  · obtain ⟨p, hp⟩ := hne
    have hlen : N.primeFactorsList.length = k := by
      simpa using (prime_tuple_perm_factors hp).length_eq.symm
    let t : Finset (List ℕ) := N.primeFactorsList.permutations.toFinset
    have hcard : (primeProductFiber k N).ncard ≤ (t : Set (List ℕ)).ncard := by
      refine Set.ncard_le_ncard_of_injOn List.ofFn ?_ List.ofFn_injective.injOn t.finite_toSet
      intro p hp
      exact List.mem_toFinset.mpr (List.mem_permutations.mpr (prime_tuple_perm_factors hp))
    rw [Set.ncard_coe_finset] at hcard
    exact hcard.trans (by simpa [t, List.length_permutations, hlen] using
      List.toFinset_card_le N.primeFactorsList.permutations)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp

/-- Restricting each coordinate to a finite prime sampling set preserves the atom bound. -/
theorem prime_sample_product_count (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (k N : ℕ) :
    (Finset.univ.filter (fun p : Fin k → S => ∏ i, (p i : ℕ) = N)).card ≤
      k.factorial := by
  classical
  let t := Finset.univ.filter (fun p : Fin k → S => ∏ i, (p i : ℕ) = N)
  have hinj : Function.Injective (fun p : Fin k → S => fun i => (p i : ℕ)) := by
    intro p q hpq
    funext i
    apply Subtype.ext
    exact congrFun hpq i
  have hcard : (t : Set (Fin k → S)).ncard ≤ (primeProductFiber k N).ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun p : Fin k → S => fun i => (p i : ℕ))
      ?_ hinj.injOn (primeProductFiber_finite k N)
    intro p hp
    refine ⟨fun i => hS (p i) (p i).property, ?_⟩
    exact (Finset.mem_filter.mp hp).2
  rw [Set.ncard_coe_finset] at hcard
  exact hcard.trans (primeProductFiber_ncard_le k N)

/-- The corresponding normalized counting measure bound. -/
theorem prime_sample_product_atom (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (k N : ℕ) :
    ((Finset.univ.filter (fun p : Fin k → S => ∏ i, (p i : ℕ) = N)).card : ℝ) /
        (S.card : ℝ) ^ k ≤ (k.factorial : ℝ) / (S.card : ℝ) ^ k := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast prime_sample_product_count S hS k N)
    (by positivity)

/-- Reduction modulo a modulus exceeding all attainable products does not merge atoms. -/
theorem prime_sample_residue_count (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (k q a : ℕ)
    (hshort : ∀ p : Fin k → S, ∏ i, (p i : ℕ) < q) :
    (Finset.univ.filter (fun p : Fin k → S => (∏ i, (p i : ℕ)) % q = a)).card ≤
      k.factorial := by
  classical
  have heq : (Finset.univ.filter (fun p : Fin k → S => (∏ i, (p i : ℕ)) % q = a)) =
      (Finset.univ.filter (fun p : Fin k → S => ∏ i, (p i : ℕ) = a)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Nat.mod_eq_of_lt (hshort p)]
  rw [heq]
  exact prime_sample_product_count S hS k a

end Problem337

end

end OAI
