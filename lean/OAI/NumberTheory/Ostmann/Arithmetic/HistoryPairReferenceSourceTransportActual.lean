import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationBlocks
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportSamples

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceSourceTransport
open Construction CanonicalOccurrenceTransport
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairRepresentativeVariables
open HistoryPairSourceCoordinates HistoryPairBulkCoordinates HistoryPairReferenceFlagsTransport
open HistoryCompensationRepresentativePatterns CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryPairReferenceFlagExpectation HistoryPairSourceFlagReplacement HistorySymbolicEncoding
local instance sourceTransportActualInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

section Decoded
variable (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ)
  (p : Pattern (pairedHistoryType seed l))
  (b : BlockDraw p (CommonSample sources (pairedInternalOrigin seed l)))
  (hvalid : ∀ i, (expand p b i).val ∈ (sources (pairedInternalOrigin seed l i)).candidates)
  (a a' : State) (f g : FrequencyChoices V l)
  (ha : Template.Matches (Template.current seed l) a.small)
  (ha' : Template.Matches (Template.current seed l) a'.small)
  {outside : List ℕ}
  (hs : (blockLeftHistory sources seed V l p b hvalid a f).Supported V outside)
  (ks : (blockRightHistory sources seed V l p b hvalid a' g).Supported V outside)
  (hperm : a.small.Perm a'.small)

theorem blockReferences_slot_values (i : Internal seed l ⊕ Internal seed l) :
    (slot (blockLeftReference sources seed V l p b hvalid a f ha hs).history
      (blockRightReference sources seed V l p b hvalid a' g ha' ks).history
      (pairedOccurrenceEquiv (blockLeftReference sources seed V l p b hvalid a f ha hs)
        (blockRightReference sources seed V l p b hvalid a' g ha' ks) i)).value=
      expand p (natBlockDraw p b Subtype.val Subtype.val_injective) i :=
  decoded_pair_slot_eq sources seed V l p b hvalid a a' f g ha ha' i

include hperm in

theorem blockReferences_root_perm :
    (blockLeftReference sources seed V l p b hvalid a f ha hs).history.root.small.Perm
      (blockRightReference sources seed V l p b hvalid a' g ha' ks).history.root.small := by
  simpa only [blockLeftReference,blockRightReference,DecodedDraw.history,decodeHistory_root] using hperm

theorem decodedSourceMean_eq_canonical (giants : Bool → PrimeSource)
    (F : (PairKey (blockLeftHistory sources seed V l p b hvalid a f)
      (blockRightHistory sources seed V l p b hvalid a' g) → ℤ) → ℝ) :
    decodedSourceMean sources seed V l p b hvalid a a' f g ha ha' hs hperm giants F=
      canonicalSourceMean (blockLeftReference sources seed V l p b hvalid a f ha hs)
        (blockRightReference sources seed V l p b hvalid a' g ha' ks) p
        (natBlockDraw p b Subtype.val Subtype.val_injective)
        (blockReferences_slot_values sources seed V l p b hvalid a a' f g ha ha' hs ks)
        (blockReferences_root_perm sources seed V l p b hvalid a a' f g ha ha' hs ks hperm) giants F :=
  actual_source_mean_eq_canonical
    (blockLeftReference sources seed V l p b hvalid a f ha hs)
    (blockRightReference sources seed V l p b hvalid a' g ha' ks) p
    (natBlockDraw p b Subtype.val Subtype.val_injective)
    (blockReferences_slot_values sources seed V l p b hvalid a a' f g ha ha' hs ks)
    (blockReferences_root_perm sources seed V l p b hvalid a a' f g ha ha' hs ks hperm) giants F

end Decoded
end Ostmann.Arithmetic.HistoryPairReferenceSourceTransport

end

end OAI
