import OAI.Combinatorics.TreeEdit.PrimeSupply
import OAI.Combinatorics.TreeEdit.FiniteTree

namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace PrimeSupply

lemma finite_lists_eventually : ∀ᶠ k : ℕ in Filter.atTop,
    ∃ p : ℕ → Fin (20 * k) → ℕ,
      (∀ j i, 0 < p j i) ∧ FiniteTree.Admissible p (k ^ 4) k 2 ∧
      (∀ j, j < k → ∀ i, p j i ≤ k ^ 5) := by
  filter_upwards [eventually_band_card 4 (by omega), Filter.eventually_ge_atTop 5] with k hk hk5
  have hcard : Fintype.card (Fin k × Fin (20 * k)) ≤ Fintype.card {p // p ∈ band k 4} := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
    have hk2 : 20 ≤ k ^ 2 := by nlinarith
    have hpow : k * (20 * k) ≤ k ^ 4 := by
      calc
        k * (20 * k) = 20 * k ^ 2 := by ring
        _ ≤ k ^ 2 * k ^ 2 := Nat.mul_le_mul_right _ hk2
        _ = k ^ 4 := by ring
    exact hpow.trans hk
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let p : ℕ → Fin (20 * k) → ℕ := fun j i => if hj : j < k then (e (⟨j, hj⟩, i)).val else 2
  have hp (j : ℕ) (hj : j < k) (i : Fin (20 * k)) :
      Nat.Prime (p j i) ∧ k ^ 4 < p j i ∧ p j i ≤ k ^ 5 := by
    simpa only [p, dite_eq_left hj] using mem_band (e (⟨j, hj⟩, i)).property
  refine ⟨p, ?_, ?_, fun j hj i => (hp j hj i).2.2⟩
  · intro j i
    by_cases hj : j < k
    · exact (hp j hj i).1.pos
    · simp [p, hj]
  · refine ⟨fun j hj i => (hp j hj i).1, fun j hj i => (hp j hj i).2.1.le, ?_, ?_⟩
    · intro j hj l hl i i' he
      have he' : e (⟨j, hj⟩, i) = e (⟨l, hl⟩, i') := by
        apply Subtype.ext
        simpa only [p, dite_eq_left hj, dite_eq_left hl] using he
      have hh := e.injective he'
      exact ⟨congrArg (fun x : Fin k × Fin (20 * k) => x.1.val) hh, congrArg Prod.snd hh⟩
    · intro j hj i
      apply (Nat.coprime_primes Nat.prime_two (hp j hj i).1).mpr
      have hkl : 2 < k ^ 4 := by nlinarith [show 5 ^ 4 ≤ k ^ 4 from Nat.pow_le_pow_left hk5 4]
      have hi := (hp j hj i).2.1
      omega

end PrimeSupply

end TreeEdit

end OAI
