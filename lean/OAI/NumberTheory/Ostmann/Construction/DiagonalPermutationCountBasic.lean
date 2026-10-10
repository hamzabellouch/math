import OAI.NumberTheory.Ostmann.Conclusion.BadArrangementCount
import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexBands

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction.DiagonalPermutationCount

abbrev BulkPosition (T : List SourceSlot) :=
  {i : RemainingIndex T // remainingPositionBand T i = some SlotRole.bulk}

abbrev NonbulkPosition (T : List SourceSlot) :=
  {i : RemainingIndex T // remainingPositionBand T i ≠ some SlotRole.bulk}

abbrev BandPermutation (T : List SourceSlot) :=
  {e : Equiv.Perm (RemainingIndex T) // PreservesRemainingBands T e}

def bulkRestriction {T : List SourceSlot} (e : BandPermutation T) :
    Equiv.Perm (BulkPosition T) :=
  e.val.subtypePerm (fun i => by rw [e.property i])

def nonbulkRestriction {T : List SourceSlot} (e : BandPermutation T) :
    Equiv.Perm (NonbulkPosition T) :=
  e.val.subtypePerm (fun i => by rw [e.property i])

theorem restrictions_injective (T : List SourceSlot) :
    Function.Injective (fun e : BandPermutation T =>
      (bulkRestriction e, nonbulkRestriction e)) := by
  intro e f h
  apply Subtype.ext
  apply Equiv.ext
  intro i
  by_cases hi : remainingPositionBand T i = some SlotRole.bulk
  · exact congrArg (fun a : Equiv.Perm (BulkPosition T) => (a ⟨i,hi⟩).val)
      (congrArg Prod.fst h)
  · exact congrArg (fun a : Equiv.Perm (NonbulkPosition T) => (a ⟨i,hi⟩).val)
      (congrArg Prod.snd h)

def orderedBulkRestriction {T : List SourceSlot} {r m : ℕ}
    (E : BulkPosition T ≃ Fin r × Fin m) (e : BandPermutation T) :
    Equiv.Perm (Fin r × Fin m) :=
  E.symm.trans ((bulkRestriction e).trans E)

theorem ordered_restrictions_injective {T : List SourceSlot} {r m : ℕ}
    (E : BulkPosition T ≃ Fin r × Fin m) :
    Function.Injective (fun e : BandPermutation T =>
      (orderedBulkRestriction E e, nonbulkRestriction e)) := by
  intro e f h
  have hn := congrArg Prod.snd h
  apply restrictions_injective T
  apply Prod.ext
  · apply Equiv.ext
    intro i
    apply E.injective
    have he := Equiv.congr_fun (congrArg Prod.fst h) (E i)
    simpa only [orderedBulkRestriction,Equiv.trans_apply,Equiv.symm_apply_apply] using he
  · exact hn

theorem ordered_bulk_fiber_card_le {T : List SourceSlot} {r m : ℕ}
    (E : BulkPosition T ≃ Fin r × Fin m) (σ : Equiv.Perm (Fin r × Fin m)) :
    Nat.card {e : BandPermutation T // orderedBulkRestriction E e = σ} ≤
      (Fintype.card (NonbulkPosition T)).factorial := by
  let f : {e : BandPermutation T // orderedBulkRestriction E e = σ} →
      Equiv.Perm (NonbulkPosition T) := fun e => nonbulkRestriction e.val
  have hf : Function.Injective f := by
    intro e g h
    apply Subtype.ext
    apply ordered_restrictions_injective E
    exact Prod.ext (e.property.trans g.property.symm) h
  simpa only [Nat.card_eq_fintype_card,Fintype.card_perm] using
    Fintype.card_le_of_injective f hf

theorem ordered_bulk_property_card_le {T : List SourceSlot} {r m : ℕ}
    (E : BulkPosition T ≃ Fin r × Fin m) (Bad : Equiv.Perm (Fin r × Fin m) → Prop) :
    Nat.card {e : BandPermutation T // Bad (orderedBulkRestriction E e)} ≤
      (Fintype.card (NonbulkPosition T)).factorial *
        Nat.card {σ : Equiv.Perm (Fin r × Fin m) // Bad σ} := by
  let f : {e : BandPermutation T // Bad (orderedBulkRestriction E e)} →
      {σ : Equiv.Perm (Fin r × Fin m) // Bad σ} × Equiv.Perm (NonbulkPosition T) :=
    fun e => (⟨orderedBulkRestriction E e.val,e.property⟩, nonbulkRestriction e.val)
  have hf : Function.Injective f := by
    intro e g h
    have hn := congrArg Prod.snd h
    have hb := congrArg (fun z => z.1.val) h
    apply Subtype.ext
    apply ordered_restrictions_injective E
    exact Prod.ext hb hn
  simpa only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_perm,Nat.mul_comm] using
    Fintype.card_le_of_injective f hf

theorem bad_arrangement_card_le {T : List SourceSlot} {r m : ℕ}
    (E : BulkPosition T ≃ Fin r × Fin m) :
    Nat.card {e : BandPermutation T // Conclusion.BadArrangement (orderedBulkRestriction E e)} ≤
      (Fintype.card (NonbulkPosition T)).factorial * Conclusion.badArrangementCount r m :=
  ordered_bulk_property_card_le E Conclusion.BadArrangement

end Ostmann.Construction.DiagonalPermutationCount

end

end OAI
