import OAI.NumberTheory.TwoPoint.Walks.ProhibitedTraceTerms

namespace OAI

/-! Exact finite reindexing of designated trace terms by their lit/unlit choice. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem prohibited_designation_sum_eq_slices {α : Type*} {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (F : Finset α) (word : α → List SignedStep)
    (label : α → Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : α → (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (keep : α → Finset (Fin R × Fin J) → Prop) :
    (∑ a ∈ F, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter (keep a),
      prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) =
    ∑ U : Finset (Fin R × Fin J),
      ∑ a ∈ F.filter (fun a => U ⊆ nonsingletonSlots (label a) ∧ keep a U),
        prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U := by
  symm
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  have hset : (univ : Finset (Finset (Fin R × Fin J))).filter
      (fun U => U ⊆ nonsingletonSlots (label a) ∧ keep a U) =
      (nonsingletonSlots (label a)).powerset.filter (keep a) := by
    ext U
    simp only [mem_filter, mem_univ, true_and, mem_powerset]
  rw [← sum_filter, hset, sum_filter]

theorem prohibited_designated_sum_eq_lit_filter {α : Type*} {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (F : Finset α) (word : α → List SignedStep)
    (label : α → Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : α → (↥(data.P ∪ data.Q) → Fin B) → ℝ) (U : Finset (Fin R × Fin J)) :
    (∑ a ∈ F, prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) =
      ∑ a ∈ F.filter (fun a => LitConsistent (nonsingletonSlots (label a) \ U) (label a)
        (tupleForcedTarget data hB (word a) (label a))),
        designatedReciprocal (fun p : ↥(data.P ∪ data.Q) => p.val)
          (singletonLabels (label a)) (nonsingletonSlots (label a) \ U) U (label a) *
          (data.residueLaw B hB).average
            (fun x => weight a x * |prohibitedWordDifference data hB s D (word a) (label a) base U x|) := by
  simp only [prohibitedDesignatedTerm, sum_filter]

theorem prohibited_designation_sum_le {α : Type*} {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (F : Finset α) (word : α → List SignedStep)
    (label : α → Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : α → (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (keep : α → Finset (Fin R × Fin J) → Prop) (A : ℝ)
    (hA : ∀ U : Finset (Fin R × Fin J),
      (∑ a ∈ F.filter (fun a => U ⊆ nonsingletonSlots (label a) ∧ keep a U),
        prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) ≤ A) :
    (∑ a ∈ F, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter (keep a),
      prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) ≤
        (2 : ℝ) ^ (R * J) * A := by
  calc
    _ = ∑ U : Finset (Fin R × Fin J),
        ∑ a ∈ F.filter (fun a => U ⊆ nonsingletonSlots (label a) ∧ keep a U),
          prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U :=
      prohibited_designation_sum_eq_slices data hB s D F word label base weight keep
    _ ≤ ∑ _U : Finset (Fin R × Fin J), A := sum_le_sum (fun U _ => hA U)
    _ = _ := by
      simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_finset, Fintype.card_prod,
        Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]

end TwoPointCorrelations

end OAI
