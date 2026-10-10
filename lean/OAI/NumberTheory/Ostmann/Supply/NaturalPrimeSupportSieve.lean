import OAI.NumberTheory.Ostmann.Supply.PrimeSupportSieve

namespace OAI

/-! # The support sieve for actual natural-number summand tails -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def naturalIntervalSet (S : Finset ℕ) (N : ℕ) : Finset (Fin (N + 1)) :=
  Finset.univ.filter fun a => a.val ∈ S

 theorem mem_naturalIntervalSet {S : Finset ℕ} {N : ℕ} {a : Fin (N + 1)} :
    a ∈ naturalIntervalSet S N ↔ a.val ∈ S := by simp [naturalIntervalSet]

 theorem naturalIntervalSet_card (S : Finset ℕ) (N : ℕ) (hS : ∀ a ∈ S, a ≤ N) :
    (naturalIntervalSet S N).card = S.card := by
  apply Finset.card_bij (fun a _ => a.val)
  · intro a ha
    exact mem_naturalIntervalSet.mp ha
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro a ha
    exact ⟨⟨a, by have := hS a ha; omega⟩, mem_naturalIntervalSet.mpr ha, rfl⟩

 theorem natural_full_support_prime_sieve (B : Set ℕ) (S P : Finset ℕ)
    (N Q : ℕ) (hS : S.Nonempty) (hbound : ∀ a ∈ S, a ≤ N) (hQ : 1 ≤ Q)
    (hP : ∀ p ∈ P, p.Prime) (hPQ : ∀ p ∈ P, p ≤ Q)
    (havoid : ∀ p ∈ P, ∀ a ∈ S, (a : ZMod p) ∉ negativeOccupiedResidues B p) :
    (∑ p ∈ P, ((occupiedResidues B p).card : ℝ) / p) ≤
      (((N + 1 : ℕ) : ℝ) + (Q : ℝ) ^ 2) / S.card := by
  have hcard := naturalIntervalSet_card S N hbound
  have hU : (naturalIntervalSet S N).Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact hS.card_pos
  have h := full_support_prime_sieve B (naturalIntervalSet S N) hU (by omega) hQ P hP hPQ
    (fun p hp a ha => havoid p hp a.val (mem_naturalIntervalSet.mp ha))
  simpa only [hcard] using h

 theorem EventuallyPrimeSumset.tail_full_support_prime_sieve {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N₀ : ℕ, ∀ X Q : ℕ, ∀ P : Finset ℕ, 1 ≤ Q →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ Q) →
      (summandTail A (N₀ + Q) X).Nonempty →
      (∑ p ∈ P, ((occupiedResidues B p).card : ℝ) / p) ≤
        (((X + 1 : ℕ) : ℝ) + (Q : ℝ) ^ 2) / (summandTail A (N₀ + Q) X).card := by
  obtain ⟨N₀, hN⟩ := h.full_residue_avoidance
  refine ⟨N₀, ?_⟩
  intro X Q P hQ hP hPQ hU
  refine natural_full_support_prime_sieve B (summandTail A (N₀ + Q) X) P X Q hU ?_ hQ hP hPQ ?_
  · intro a ha
    exact (mem_summandTail A (N₀ + Q) X a).mp ha |>.2.2
  · intro p hp a ha
    obtain ⟨haA, hlarge, _⟩ := (mem_summandTail A (N₀ + Q) X a).mp ha
    exact hN p (hP p hp) a haA (by have := hPQ p hp; omega)

end Ostmann

end OAI
