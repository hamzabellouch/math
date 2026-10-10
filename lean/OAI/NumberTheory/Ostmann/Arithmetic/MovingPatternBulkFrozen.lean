import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkData
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenSupportedArithmetic

namespace OAI

/-! # The original pattern has fixed nonbulk data under bulk resampling -/

namespace Ostmann
open scoped Classical

theorem movingPatternBulkEmbedding_external_mem {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (slot : (TreeLeafIndex n × Fin m) ↪ B) (b : B) :
    e.symm (.inl b) ∈ Set.range (movingPatternBulkEmbedding e slot) ↔ b ∈ Set.range slot := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, Sum.inl.inj (e.symm.injective hj)⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, rfl⟩

theorem movingPatternBulkEmbedding_internal_absent {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (slot : (TreeLeafIndex n × Fin m) ↪ B) (c : C) :
    e.symm (.inr c) ∉ Set.range (movingPatternBulkEmbedding e slot) := by
  rintro ⟨j, hj⟩
  have h := e.symm.injective hj
  cases h

theorem movingPatternFiniteSmall_absent {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (small : TreeLeafTuple (List B) n)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot) :
    ∀ i ∈ flattenMovingSlots n (movingPatternFiniteSmall e n small),
      i ∉ Set.range (movingPatternBulkEmbedding e slot) := by
  intro i hi
  rw [movingPatternFiniteSmall, flattenMovingSlots_map] at hi
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hi
  exact fun h => hsmall b hb ((movingPatternBulkEmbedding_external_mem e slot b).mp h)

theorem movingPattern_nonbulk_values {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (base value : Fin (N + 1) → ℕ)
    (hv : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), value i = base i)
    (small : TreeLeafTuple (List B) n) (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (side : Bool) :
    movingSlotValues value n (movingPatternFiniteSmall e n small) =
        movingSlotValues base n (movingPatternFiniteSmall e n small) ∧
      (movingPatternFiniteSamples e n pattern side).values value =
        (movingPatternFiniteSamples e n pattern side).values base := by
  apply frozenMoving_nonbulk_values ((Sum.elim tierB tierC) ∘ e) base value
    (movingPatternBulkEmbedding e slot) n _ hv _ _
    (movingPatternFiniteSmall_absent e slot small hsmall)
    (movingPatternFiniteSamples_levels e tierB tierC n pattern htier side)
  intro j
  change n ≤ Sum.elim tierB tierC (e (e.symm (.inl (slot j))))
  simpa only [Equiv.apply_symm_apply, Sum.elim_inl] using hB (slot j)

theorem movingPatternFinBulkData_bulk_nodup {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2) :
    ∀ b, ∀ L ∈ (movingPatternFinBulkData e n m t small slot perm pattern b).regularLists,
      (L.filter (bulkIndexPredicate (movingPatternBulkEmbedding e slot))).Nodup := by
  let lift := movingPatternBulkEmbedding e slot
  let tier := (Sum.elim tierB tierC) ∘ e
  have hgrade (i) (hi : bulkIndexPredicate lift i = true) : n ≤ tier i := by
    obtain ⟨j, rfl⟩ := (bulkIndexPredicate_eq_true lift i).mp hi
    change n ≤ Sum.elim tierB tierC (e (e.symm (.inl (slot j))))
    simpa only [Equiv.apply_symm_apply, Sum.elim_inl] using hB (slot j)
  have hs (b) (i) (hi : i ∈ flattenMovingSlots n (movingPatternFiniteSmall e n (small b))) :
      bulkIndexPredicate lift i = false :=
    (bulkIndexPredicate_eq_false lift i).mpr (movingPatternFiniteSmall_absent e slot _ (hsmall b) i hi)
  have hst (b) (i) (hi : i ∈ flattenMovingSlots n (movingPatternFiniteSmall e n (small b))) :
      n ≤ tier i := by
    rw [movingPatternFiniteSmall, flattenMovingSlots_map] at hi
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    simpa only [tier, Function.comp_apply, Equiv.apply_symm_apply, Sum.elim_inl] using hB j
  intro b
  rw [movingPatternFinBulkData_build]
  cases b
  · exact buildMovingSlotData_bulk_nodup n m (bulkIndexPredicate lift) tier lift
      (fun j => (bulkIndexPredicate_eq_true lift _).mpr ⟨j, rfl⟩) hgrade
      (t false) (movingPatternFiniteSmall e n (small false))
      (movingPatternFiniteSamples e n pattern false) (hs false) (hst false)
      (movingPatternFiniteSamples_levels e tierB tierC n pattern htier false)
  · exact buildMovingSlotData_bulk_nodup n m (bulkIndexPredicate lift) tier
      (perm.symm.toEmbedding.trans lift)
      (fun j => (bulkIndexPredicate_eq_true lift _).mpr ⟨perm.symm j, rfl⟩) hgrade
      (t true) (movingPatternFiniteSmall e n (small true))
      (movingPatternFiniteSamples e n pattern true) (hs true) (hst true)
      (movingPatternFiniteSamples_levels e tierB tierC n pattern htier true)

end Ostmann

end OAI
