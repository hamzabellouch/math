import OAI.Probability.MatroidProphet.Main
import Mathlib.Data.Fintype.EquivFin

namespace OAI

/-!
# Timestamp representations of finite insertion orders

The marked-pivot proof uses injective natural-number timestamps, whereas the
manuscript speaks about positions in a finite interleaving. We prove that
timestamps can be normalized to a permutation of the finite position set
without changing any prefix, first-spanning pivot, or recorded mark vector.
No bound on gaps between timestamps is imposed.
-/

namespace MatroidProphet.Pivots

open Set Finset

variable {α β : Type*} [Fintype β]

/-- The position of an occurrence is the number of its strict predecessors. -/
noncomputable def orderPosition (time : β → ℕ) (o : β) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p => time p < time o)).card

lemma orderPosition_mono (time : β → ℕ) {o p : β} (h : time o ≤ time p) :
    orderPosition time o ≤ orderPosition time p := by
  classical
  apply Finset.card_le_card
  intro a ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    lt_of_lt_of_le (Finset.mem_filter.mp ha).2 h⟩

lemma orderPosition_strict (time : β → ℕ) {o p : β} (h : time o < time p) :
    orderPosition time o < orderPosition time p := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_trans (Finset.mem_filter.mp ha).2 h⟩
  · intro heq
    have ho : o ∈ Finset.univ.filter (fun a => time a < time p) := by simp [h]
    rw [← heq] at ho
    simp at ho

lemma orderPosition_lt_iff (time : β → ℕ) (o p : β) :
    orderPosition time o < orderPosition time p ↔ time o < time p := by
  refine ⟨?_, orderPosition_strict time⟩
  intro h
  by_contra hn
  exact (not_lt_of_ge (orderPosition_mono time (Nat.le_of_not_gt hn))) h

lemma orderPosition_le_iff (time : β → ℕ) (o p : β) :
    orderPosition time o ≤ orderPosition time p ↔ time o ≤ time p := by
  simp only [← not_lt, orderPosition_lt_iff]

lemma orderPosition_lt_card (time : β → ℕ) (o : β) :
    orderPosition time o < Fintype.card β := by
  classical
  change (Finset.univ.filter (fun p => time p < time o)).card < Fintype.card β
  rw [← Finset.card_univ]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  have ho : o ∈ (Finset.univ : Finset β) := Finset.mem_univ _
  rw [← heq] at ho
  simp at ho

/-- The normalized timestamp lies in the actual finite position set. -/
noncomputable def finiteOrderPosition (time : β → ℕ) (o : β) : Fin (Fintype.card β) :=
  ⟨orderPosition time o, orderPosition_lt_card time o⟩

lemma finiteOrderPosition_injective (time : β → ℕ) (htime : Function.Injective time) :
    Function.Injective (finiteOrderPosition time) := by
  intro o p heq
  apply htime
  have hval := congrArg Fin.val heq
  change orderPosition time o = orderPosition time p at hval
  apply Nat.le_antisymm
  · exact (orderPosition_le_iff time o p).mp hval.le
  · exact (orderPosition_le_iff time p o).mp hval.ge

lemma finiteOrderPosition_bijective (time : β → ℕ) (htime : Function.Injective time) :
    Function.Bijective (finiteOrderPosition time) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨finiteOrderPosition_injective time htime, by simp⟩

omit [Fintype β] in
/-- Only the relative occurrence order, not the timestamp magnitudes, matters. -/
lemma isPivot_iff_of_same_order (M : Matroid α) (label : β → α)
    (time time' : β → ℕ) (horder : ∀ o p, time o < time p ↔ time' o < time' p)
    (e : α) (o : β) : IsPivot M label time e o ↔ IsPivot M label time' e o := by
  have hbefore : {p | time p < time o} = {p | time' p < time' o} := by
    ext p
    exact horder p o
  have hthrough : {p | time p ≤ time o} = {p | time' p ≤ time' o} := by
    ext p
    simp only [mem_ofPred_eq, ← not_lt, horder o p]
  simp only [IsPivot, hbefore, hthrough]

lemma isPivot_orderPosition_iff (M : Matroid α) (label : β → α)
    (time : β → ℕ) (e : α) (o : β) :
    IsPivot M label (orderPosition time) e o ↔ IsPivot M label time e o :=
  isPivot_iff_of_same_order M label (orderPosition time) time
    (orderPosition_lt_iff time) e o

lemma recordsPivots_orderPosition_iff {r q n : ℕ} (M : Matroid α)
    (label : Occurrence r q → α) (test : Fin n → α) (time : Occurrence r q → ℕ)
    (oldMark : Fin r → Bool) (movableMark : Fin q → Bool) (t : Finset (Fin n)) :
    RecordsPivots M label test (orderPosition time) oldMark movableMark t ↔
      RecordsPivots M label test time oldMark movableMark t := by
  simp only [RecordsPivots, isPivot_orderPosition_iff]

lemma oldOrdered_orderPosition_iff {r q : ℕ} (time : Occurrence r q → ℕ) :
    OldOrdered (orderPosition time) ↔ OldOrdered time := by
  simp only [OldOrdered, orderPosition_lt_iff]

/-- The counted family is exactly the family obtained from genuine finite
interleavings. Arbitrary natural-number gaps neither add nor remove patterns. -/
lemma mem_markedPivotPatterns_iff_finite_order [Fintype α] {r q n : ℕ}
    (M : Matroid α) (b : ℕ → α) (a : Fin q → α) (test : Fin n → α)
    (oldMark : Fin r → Bool) (t : Finset (Fin n)) :
    t ∈ markedPivotPatterns M b a test oldMark ↔
      ∃ position : Occurrence r q ≃ Fin (Fintype.card (Occurrence r q)),
        OldOrdered (fun o => (position o).val) ∧
          ∃ movableMark : Fin q → Bool,
            RecordsPivots M (occurrenceLabel b a) test (fun o => (position o).val)
              oldMark movableMark t := by
  classical
  constructor
  · intro ht
    obtain ⟨time, horder, htime, movableMark, hrecords⟩ := (Finset.mem_filter.mp ht).2
    let position := Equiv.ofBijective (finiteOrderPosition time)
      (finiteOrderPosition_bijective time htime)
    refine ⟨position, ?_, movableMark, ?_⟩
    · change OldOrdered (orderPosition time)
      exact (oldOrdered_orderPosition_iff time).mpr horder
    · change RecordsPivots M (occurrenceLabel b a) test (orderPosition time)
        oldMark movableMark t
      exact (recordsPivots_orderPosition_iff M (occurrenceLabel b a) test time
        oldMark movableMark t).mpr hrecords
  · rintro ⟨position, horder, movableMark, hrecords⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (fun o => (position o).val),
      horder, (fun o p h => position.injective (Fin.ext h)), movableMark, hrecords⟩

end MatroidProphet.Pivots

end OAI
