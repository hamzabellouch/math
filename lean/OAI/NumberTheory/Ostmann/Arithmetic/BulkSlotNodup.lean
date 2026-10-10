import Mathlib.Data.List.FinRange
import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkNodup
import OAI.NumberTheory.Ostmann.Arithmetic.BulkSlotFieldBridge

namespace OAI

/-! # Distinct selected bulk labels in the concrete leaf constructor -/

namespace Ostmann
open scoped Classical

theorem mem_flatten_bulkSlotLeaves {σ : Type*} (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → σ) (i : σ) :
    i ∈ flattenMovingSlots n (bulkSlotLeaves n m slot) ↔ ∃ j, slot j = i := by
  induction n with
  | zero =>
    change i ∈ List.ofFn (fun j => slot ((), j)) ↔ ∃ j, slot j = i
    rw [List.mem_ofFn]
    constructor
    · rintro ⟨j, hj⟩; exact ⟨((), j), hj⟩
    · rintro ⟨⟨u, j⟩, hj⟩; cases u; exact ⟨j, hj⟩
  | succ n ih =>
    change i ∈ (flattenMovingSlots n (bulkSlotLeaves n m (fun j => slot (.inl j.1, j.2))) ++
      flattenMovingSlots n (bulkSlotLeaves n m (fun j => slot (.inr j.1, j.2)))) ↔ _
    rw [List.mem_append, ih, ih]
    constructor
    · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
      · exact ⟨(.inl j.1, j.2), hj⟩
      · exact ⟨(.inr j.1, j.2), hj⟩
    · rintro ⟨⟨j | j, k⟩, h⟩
      · exact Or.inl ⟨(j, k), h⟩
      · exact Or.inr ⟨(j, k), h⟩

theorem bulkSlotLeaves_nodup {σ : Type*} (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → σ) (hinj : Function.Injective slot) :
    (flattenMovingSlots n (bulkSlotLeaves n m slot)).Nodup := by
  induction n with
  | zero =>
    apply List.nodup_ofFn_ofInjective
    intro i j h
    exact congrArg Prod.snd (hinj h)
  | succ n ih =>
    change (flattenMovingSlots n (bulkSlotLeaves n m (fun j => slot (.inl j.1, j.2))) ++
      flattenMovingSlots n (bulkSlotLeaves n m (fun j => slot (.inr j.1, j.2)))).Nodup
    refine List.nodup_append.mpr ⟨ih _ ?_, ih _ ?_, ?_⟩
    · intro i j h
      have h' := hinj h
      have hi : i.1 = j.1 := Sum.inl.inj
        (congrArg (fun x : TreeLeafIndex (n + 1) × Fin m => x.1) h')
      have hj : i.2 = j.2 := congrArg (fun x : TreeLeafIndex (n + 1) × Fin m => x.2) h'
      exact Prod.ext hi hj
    · intro i j h
      have h' := hinj h
      have hi : i.1 = j.1 := Sum.inr.inj
        (congrArg (fun x : TreeLeafIndex (n + 1) × Fin m => x.1) h')
      have hj : i.2 = j.2 := congrArg (fun x : TreeLeafIndex (n + 1) × Fin m => x.2) h'
      exact Prod.ext hi hj
    · intro a ha b hb hab
      obtain ⟨j, hj⟩ := (mem_flatten_bulkSlotLeaves n m _ a).mp ha
      obtain ⟨k, hk⟩ := (mem_flatten_bulkSlotLeaves n m _ b).mp hb
      have h' := congrArg Prod.fst (hinj (hj.trans (hab.trans hk.symm)))
      cases h'

theorem buildMovingSlotData_root_bulk_nodup {σ : Type*} (n m : ℕ)
    (bulk : σ → Bool) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (hbulk : ∀ j, bulk (slot j) = true)
    (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, bulk i = false) :
    ((buildMovingSlotData n t small (bulkSlotLeaves n m slot) samples).regularSlots.filter bulk).Nodup := by
  have hs : (flattenMovingSlots n small).filter bulk = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro i hi
    simp [hsmall i hi]
  have hb : (flattenMovingSlots n (bulkSlotLeaves n m slot)).filter bulk =
      flattenMovingSlots n (bulkSlotLeaves n m slot) := by
    apply List.filter_eq_self.mpr
    intro i hi
    obtain ⟨j, rfl⟩ := (mem_flatten_bulkSlotLeaves n m slot i).mp hi
    exact hbulk j
  have hp := (buildMovingSlotData_regular_perm n t small (bulkSlotLeaves n m slot) samples).filter bulk
  rw [List.filter_append, hs, List.nil_append, hb] at hp
  exact hp.nodup_iff.mpr (bulkSlotLeaves_nodup n m slot slot.injective)

theorem buildMovingSlotData_bulk_nodup {σ : Type*} (n m : ℕ)
    (bulk : σ → Bool) (tier : σ → ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (hbulk : ∀ j, bulk (slot j) = true) (htier : ∀ i, bulk i = true → n ≤ tier i)
    (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, bulk i = false)
    (hsmallTier : ∀ i ∈ flattenMovingSlots n small, n ≤ tier i)
    (hsamples : samples.Levels tier) :
    ∀ L ∈ (buildMovingSlotData n t small (bulkSlotLeaves n m slot) samples).regularLists,
      (L.filter bulk).Nodup := by
  have hlevels := buildMovingSlotData_levels tier n t small (bulkSlotLeaves n m slot) samples
    hsmallTier (fun i hi => by
      obtain ⟨j, rfl⟩ := (mem_flatten_bulkSlotLeaves n m slot i).mp hi
      exact htier _ (hbulk j)) hsamples
  apply MovingSlotData.regularLists_bulk_nodup bulk _
    (buildMovingSlotData_regular_coherent n t small (bulkSlotLeaves n m slot) samples)
  · intro i hi
    exact MovingSlotData.compensationAbsent_of_levels tier _ hlevels i (htier i hi)
  · exact buildMovingSlotData_root_bulk_nodup n m bulk slot hbulk t small samples hsmall

theorem bulk_value_injective {σ J : Type*} (value : σ → ℕ) (bulk : σ → Bool)
    (slot : J → σ) (hcover : ∀ i, bulk i = true → ∃ j, slot j = i)
    (hinj : Function.Injective (value ∘ slot)) :
    ∀ i j, bulk i = true → bulk j = true → value i = value j → i = j := by
  intro i j hi hj hv
  obtain ⟨a, rfl⟩ := hcover i hi
  obtain ⟨b, rfl⟩ := hcover j hj
  exact congrArg slot (hinj hv)

end Ostmann

end OAI
