import OAI.NumberTheory.TwoPoint.Bounds.CompressedRuns
import OAI.NumberTheory.TwoPoint.Bounds.RunPartitionProperties

namespace OAI

/-! Every observed regular class is present in an encoded regular segment. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]

/-- Greedy compression can suppress only the preceding label; no observed
class disappears from the previous-label/run-head pair. -/
theorem columnRunHeads_cover (l : List α) (previous : Option α) (a : α) (ha : a ∈ l) :
    previous = some a ∨ a ∈ columnRunHeads (l.map some) previous := by
  induction l generalizing previous with
  | nil => simp at ha
  | cons b rest ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · by_cases hp : previous = some a
        · exact Or.inl hp
        · exact Or.inr (by simp [columnRunHeads, hp])
      · rcases ih (some b) ha with heq | hm
        · have hab : b = a := Option.some.inj heq
          subst b
          by_cases hp : previous = some a
          · exact Or.inl hp
          · exact Or.inr (by simp [columnRunHeads, hp])
        · exact Or.inr (by
            simp only [List.map_cons, columnRunHeads]
            split_ifs <;> simp [hm])

theorem mem_columnRunHeads (l : List α) (a : α) (ha : a ∈ l) :
    a ∈ columnRunHeads (l.map some) none := by
  exact (columnRunHeads_cover l none a ha).resolve_left (by simp)

omit [DecidableEq α] in
/-- A regular observed run occurs in one of the actual regular pieces,
so the shared forest numbering applies to it. -/
theorem partitionColumnRuns_regular_cover (omitted : α → Bool) (runs : List α)
    (a : α) (ha : a ∈ runs) (hregular : omitted a = false) :
    ∃ segment, Sum.inl segment ∈ partitionColumnRuns omitted runs ∧ a ∈ segment := by
  have hflat : a ∈ (partitionColumnRuns omitted runs).flatMap (Sum.elim id List.singleton) := by
    rwa [partitionColumnRuns_flatten]
  obtain ⟨piece, hp, ha⟩ := List.mem_flatMap.mp hflat
  cases piece with
  | inl segment => exact ⟨segment, hp, ha⟩
  | inr b =>
      have hab : a = b := List.mem_singleton.mp ha
      subst b
      have hm : a ∈ (partitionColumnRuns omitted runs).filterMap (Sum.elim (fun _ => none) some) :=
        List.mem_filterMap.mpr ⟨.inr a, hp, rfl⟩
      rw [partitionColumnRuns_omitted] at hm
      have ht := (List.mem_filter.mp hm).2
      simp [hregular] at ht

end TwoPointCorrelations

end OAI
