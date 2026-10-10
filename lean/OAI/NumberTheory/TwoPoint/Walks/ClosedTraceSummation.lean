import OAI.NumberTheory.TwoPoint.Walks.ClosedTraceEncoding

namespace OAI

/-! Partition the actual path-pair catalog by its signs without multiplicity loss. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def closedTraceFiber {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (F : Finset ((Fin k → ((j : Fin J) → P j) × (Q × Bool)) ×
      (Fin k → ((j : Fin J) → P j) × (Q × Bool)))) (forward : Fin (2 * k) → Bool) :
    Finset (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) :=
  (F.filter (fun p => (closedTraceEncoding Q p).1 = forward)).image
    (fun p => (closedTraceEncoding Q p).2)

lemma mem_closedTraceFiber {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (F : Finset ((Fin k → ((j : Fin J) → P j) × (Q × Bool)) ×
      (Fin k → ((j : Fin J) → P j) × (Q × Bool)))) (forward : Fin (2 * k) → Bool)
    (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) :
    a ∈ closedTraceFiber Q F forward ↔
      ∃ p ∈ F, (closedTraceEncoding Q p).1 = forward ∧ (closedTraceEncoding Q p).2 = a := by
  simp only [closedTraceFiber, mem_image, mem_filter]
  constructor
  · rintro ⟨p, ⟨hp, hf⟩, ha⟩
    exact ⟨p, hp, hf, ha⟩
  · rintro ⟨p, hp, hf, ha⟩
    exact ⟨p, ⟨hp, hf⟩, ha⟩

lemma closedTraceFiber_word {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (F : Finset ((Fin k → ((j : Fin J) → P j) × (Q × Bool)) ×
      (Fin k → ((j : Fin J) → P j) × (Q × Bool)))) (forward : Fin (2 * k) → Bool)
    (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q))
    (ha : a ∈ closedTraceFiber Q F forward) :
    ∃ p ∈ F, columnTupleWord a.1 forward (fun i => (a.2 i).val) =
      integerClosedWordCode Q (fun d => ∏ j, (d j).val) p := by
  obtain ⟨p, hp, hf, he⟩ := (mem_closedTraceFiber Q F forward a).mp ha
  refine ⟨p, hp, ?_⟩
  simpa only [hf, he] using closedTraceEncoding_word Q p

theorem sum_closedTraceFiber {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (F : Finset ((Fin k → ((j : Fin J) → P j) × (Q × Bool)) ×
      (Fin k → ((j : Fin J) → P j) × (Q × Bool))))
    (term : (Fin (2 * k) → Bool) →
      (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) → ℝ) :
    (∑ p ∈ F, term (closedTraceEncoding Q p).1 (closedTraceEncoding Q p).2) =
      ∑ forward, ∑ a ∈ closedTraceFiber Q F forward, term forward a := by
  symm
  calc
    _ = ∑ forward, ∑ p ∈ F.filter (fun p => (closedTraceEncoding Q p).1 = forward),
        term (closedTraceEncoding Q p).1 (closedTraceEncoding Q p).2 := by
      apply sum_congr rfl
      intro forward _
      unfold closedTraceFiber
      rw [sum_image]
      · apply sum_congr rfl
        intro p hp
        rw [(mem_filter.mp hp).2]
      · intro a ha b hb hab
        apply closedTraceEncoding_injective Q hprime hdisjoint
        exact Prod.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm) hab
    _ = _ := sum_fiberwise F (fun p => (closedTraceEncoding Q p).1)
      (fun p => term (closedTraceEncoding Q p).1 (closedTraceEncoding Q p).2)

end TwoPointCorrelations

end OAI
