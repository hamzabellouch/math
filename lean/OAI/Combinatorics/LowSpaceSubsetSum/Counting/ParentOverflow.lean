import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationParentComplete

namespace OAI

/-! # Exact overflow decisions for the distinct-entry analysis universe -/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationParentData

variable {n : ℕ} (D : RepresentationParentData n)

def entryUniverse : Finset (Entry (Fin n)) := by
  classical
  exact D.rawEntries.toFinset

theorem entries_nodup (B : ℕ) : (D.entries B).toList.Nodup := by
  classical
  have h := D.collect_invariant B
  have hk : (((D.entries B).toList.map (WeightEncoding.entryKey D.input)).toFinset).card =
      ((D.entries B).toList.map (WeightEncoding.entryKey D.input)).length := by
    unfold entries
    rw [← h.keys_eq, BinaryTrie.card_keySet, ← h.size_eq, List.length_map, Array.length_toList]
  have hm : ((D.entries B).toList.map (WeightEncoding.entryKey D.input)).Nodup :=
    List.nodup_iff_length_dedup_eq.mpr (by rwa [← List.card_toFinset])
  exact List.Nodup.of_map (WeightEncoding.entryKey D.input) hm

theorem completed_size_le (B : ℕ) (hc : (D.collect B).state.user.keys.overflow = false) :
    (D.entries B).size ≤ D.capacity := by
  rw [entries, (D.collect_invariant B).size_eq]
  exact (D.collect_invariant B).safe.complete_bound hc

theorem completed_size_eq_card (B : ℕ)
    (hbounded : ∀ e ∈ D.rawEntries, WeightEncoding.BoundedWeight D.input e.value)
    (hc : (D.collect B).state.user.keys.overflow = false) :
    (D.entries B).size = D.entryUniverse.card := by
  classical
  have he : (D.entries B).toList.toFinset = D.entryUniverse := by
    ext e
    simp only [List.mem_toFinset, entryUniverse, D.entries_mem_iff_of_complete B hc hbounded]
  rw [← he, List.toFinset_card_of_nodup (D.entries_nodup B), Array.length_toList]

theorem collect_clear_iff_card (B : ℕ)
    (hbounded : ∀ e ∈ D.rawEntries, WeightEncoding.BoundedWeight D.input e.value) :
    (D.collect B).state.user.keys.overflow = false ↔ D.entryUniverse.card ≤ D.capacity := by
  classical
  constructor
  · intro hc
    have hm := D.entries_mem_iff_of_complete B hc hbounded
    have hsub : D.entryUniverse ⊆ (D.entries B).toList.toFinset := by
      intro e he
      exact List.mem_toFinset.mpr ((hm e).mpr (List.mem_toFinset.mp he))
    calc
      D.entryUniverse.card ≤ (D.entries B).toList.toFinset.card := Finset.card_le_card hsub
      _ ≤ (D.entries B).toList.length := List.toFinset_card_le _
      _ = (D.entries B).size := Array.length_toList
      _ ≤ D.capacity := by
        rw [entries, (D.collect_invariant B).size_eq]
        exact (D.collect_invariant B).safe.complete_bound hc
  · intro hc
    exact (D.collect_fits B D.entryUniverse hc (fun e he => List.mem_toFinset.mpr he)).1

theorem collect_overflow_iff_card (B : ℕ)
    (hbounded : ∀ e ∈ D.rawEntries, WeightEncoding.BoundedWeight D.input e.value) :
    (D.collect B).state.user.keys.overflow = true ↔ D.capacity < D.entryUniverse.card := by
  rw [← not_le, ← D.collect_clear_iff_card B hbounded]
  cases (D.collect B).state.user.keys.overflow <;> simp

end LowSpaceSubsetSum.RepresentationParentData

end

end OAI
