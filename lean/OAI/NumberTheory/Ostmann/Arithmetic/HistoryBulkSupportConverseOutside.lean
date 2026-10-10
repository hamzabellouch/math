import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeSourceSeparationModuli
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedXiTransportBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction HistoryOccurrenceVariables HistoryRepresentativeSourceSeparation
open HistorySignedXiTransport

theorem internalSlot_mem_internalOccurrences {l : ℕ} (h : History l) (i : InternalKey h) :
    internalSlot h i ∈ h.internalOccurrences := by
  induction h with
  | leaf a => exact Empty.elim i
  | node a p u hp hm left right il ir =>
    rcases i with i | i | i
    · exact List.mem_append_left _ (List.mem_append_left _ (List.get_mem u i))
    · exact List.mem_append_left _ (List.mem_append_right _ (il i))
    · exact List.mem_append_right _ (ir i)

theorem internalOccurrences_coprime_outside_of_supported
    {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ} {h : History l}
    (hs : h.Supported V outside) :
    ∀ z ∈ h.internalOccurrences, Nat.Coprime z.value outside.prod := by
  induction h with
  | leaf a => simp only [History.internalOccurrences,List.not_mem_nil,forall_false,implies_true]
  | node a p u hp hm left right il ir =>
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · rcases List.mem_append.mp hz with hz | hz
      · exact rootSlot_coprime_outside left (History.supported_left hs) z
          ((History.supported_child_small hs).1.mem_iff.mpr (List.mem_append_left _ hz))
      · exact il (History.supported_left hs) z hz
    · exact ir (History.supported_right hs) z hz

theorem internal_outside_product_coprime_decode_redraw
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    {outside : List ℕ} (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (i : InternalKey (decodeHistory sources seed V l b c)) :
    Nat.Coprime (internalSlot (decodeHistory sources seed V l b c) i).value outside.prod := by
  apply internalOccurrences_coprime_outside_of_supported hs
  rw [decoded_internalOccurrences_eq sources seed V l a b c]
  exact internalSlot_mem_internalOccurrences _ i

theorem internal_outside_coprime_decode_redraw
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    {outside : List ℕ} (hs : (decodeHistory sources seed V l a c).Supported V outside) :
    ∀ i : InternalKey (decodeHistory sources seed V l b c), ∀ q ∈ outside,
      Nat.Coprime (internalSlot (decodeHistory sources seed V l b c) i).value q := by
  intro i q hq
  exact Nat.coprime_list_prod_right_iff.mp
    (internal_outside_product_coprime_decode_redraw sources seed V l a b c hs i) q hq

theorem internal_outside_coprime_assigned_redraw
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ)
    (x y : SourceAssignment sources (Template.current seed l))
    (s t : ℤ) (Gp Gm Gp' Gm' : ℕ) (c : HistoryChoices sources seed V l)
    {outside : List ℕ}
    (hs : (decodeHistory sources seed V l
      ⟨s,Gp,Gm,assignedSlots sources (Template.current seed l) x⟩ c).Supported V outside) :
    ∀ i : InternalKey (decodeHistory sources seed V l
      ⟨t,Gp',Gm',assignedSlots sources (Template.current seed l) y⟩ c), ∀ q ∈ outside,
      Nat.Coprime (internalSlot (decodeHistory sources seed V l
        ⟨t,Gp',Gm',assignedSlots sources (Template.current seed l) y⟩ c) i).value q :=
  internal_outside_coprime_decode_redraw sources seed V l _ _ c hs

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
