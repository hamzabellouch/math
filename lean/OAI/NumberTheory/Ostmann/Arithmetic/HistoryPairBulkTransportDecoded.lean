import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkTransportBasic
import OAI.NumberTheory.Ostmann.Conclusion.SourcePermutation
import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoicesValues

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairBulkTransport
open Construction Construction.CanonicalOccurrenceTransport HistorySymbolicEncoding
open CompensationEqualityPatterns
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

def pairedDrawValues (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ)
    (c d : HistoryChoices sources seed V l) : Internal seed l ⊕ Internal seed l → ℕ :=
  Sum.elim (fun i => (historyDraws sources seed V l c i).val)
    (fun i => (historyDraws sources seed V l d i).val)

def pairedDrawPattern (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ)
    (c d : HistoryChoices sources seed V l) : Pattern (pairedHistoryType seed l) :=
  patternOf (pairedHistoryType seed l) (pairedDrawValues sources seed V l c d)

theorem internalPairSample_decode (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a b : State) (c d : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (i : Internal seed l ⊕ Internal seed l) :
    internalPairSample seed (decodeHistory sources seed V l a c) (decodeHistory sources seed V l b d)
      (decoded_tree_source_labels sources seed V l a c ha)
      (decoded_tree_source_labels sources seed V l b d hb) i =
      (pairedDrawValues sources seed V l c d i : ℤ) := by
  cases i with
  | inl i => exact decoded_coordinateSample_internal sources seed V l a c ha i
  | inr i => exact decoded_coordinateSample_internal sources seed V l b d hb i

theorem coordinateSample_root_assigned (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (x : SourceAssignment sources (Template.current seed l))
    (hx : a.small = assignedSlots sources (Template.current seed l) x)
    (ha : Template.Matches (Template.current seed l) a.small)
    (i : Fin (Template.current seed l).length) :
    coordinateSample seed (decodeHistory sources seed V l a c)
      (decoded_tree_source_labels sources seed V l a c ha) (.inr (.inl i)) = (x i).val := by
  simp only [coordinateSample, Function.comp_apply, coordinateEquiv,
    Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, HistoryOccurrenceVariables.integerSample]
  simp [hx, assignedSlots, Template.sample]

theorem samePairPattern_decoded (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ) (a b a' b' : State)
    (c d c' d' : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (ha' : Template.Matches (Template.current seed l) a'.small)
    (hb' : Template.Matches (Template.current seed l) b'.small)
    (hc : (decodeHistory sources seed V l a c).Supported V outside)
    (hc' : (decodeHistory sources seed V l a' c').Supported V outside)
    (σ : Equiv.Perm (Fin (Template.current seed l).length))
    (hroot : ∀ i,
      coordinateSample seed (decodeHistory sources seed V l b d)
        (decoded_tree_source_labels sources seed V l b d hb) (.inr (.inl i)) =
      coordinateSample seed (decodeHistory sources seed V l a c)
        (decoded_tree_source_labels sources seed V l a c ha) (.inr (.inl (σ i))))
    (hroot' : ∀ i,
      coordinateSample seed (decodeHistory sources seed V l b' d')
        (decoded_tree_source_labels sources seed V l b' d' hb') (.inr (.inl i)) =
      coordinateSample seed (decodeHistory sources seed V l a' c')
        (decoded_tree_source_labels sources seed V l a' c' ha') (.inr (.inl (σ i))))
    (hpattern : pairedDrawPattern sources seed V l c d = pairedDrawPattern sources seed V l c' d') :
    SamePairPattern seed
      (decodeHistory sources seed V l a c) (decodeHistory sources seed V l b d)
      (decodeHistory sources seed V l a' c') (decodeHistory sources seed V l b' d')
      (decoded_tree_source_labels sources seed V l a c ha)
      (decoded_tree_source_labels sources seed V l b d hb)
      (decoded_tree_source_labels sources seed V l a' c' ha')
      (decoded_tree_source_labels sources seed V l b' d' hb') := by
  apply samePairPattern_of_root_permutation seed _ _ _ _ hc hc'
    (decoded_tree_source_labels sources seed V l a c ha)
    (decoded_tree_source_labels sources seed V l b d hb)
    (decoded_tree_source_labels sources seed V l a' c' ha')
    (decoded_tree_source_labels sources seed V l b' d' hb') σ hroot hroot' 
  intro i j
  rw [internalPairSample_decode sources seed V l a b c d ha hb i,
    internalPairSample_decode sources seed V l a b c d ha hb j,
    internalPairSample_decode sources seed V l a' b' c' d' ha' hb' i,
    internalPairSample_decode sources seed V l a' b' c' d' ha' hb' j]
  simp only [Int.natCast_inj]
  have he : (pairedDrawPattern sources seed V l c d).val.r i j ↔
      (pairedDrawPattern sources seed V l c' d').val.r i j := by rw [hpattern]
  change ((pairedHistoryType seed l i, pairedDrawValues sources seed V l c d i) =
    (pairedHistoryType seed l j, pairedDrawValues sources seed V l c d j) ↔
    (pairedHistoryType seed l i, pairedDrawValues sources seed V l c' d' i) =
    (pairedHistoryType seed l j, pairedDrawValues sources seed V l c' d' j)) at he
  simpa only [Prod.mk.injEq] using he

end Ostmann.Arithmetic.HistoryPairBulkTransport

end

end OAI
