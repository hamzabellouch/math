import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsSupportTransport
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsSupportUpdate

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceLaws
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceCoordinates HistoryCompensationRepresentativePatterns
open HistoryPairPattern HistoryPairRows HistoryPairRepresentativeVariables HistoryPairKernelReplacement
attribute [local instance] Classical.propDecidable
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

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
  (hperm : a.small.Perm a'.small)

theorem decoded_block_update_coordinate (q : Block p) :
    decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm
        (.inr (.inr q)) =
      representativeMap (blockLeftHistory sources seed V l p b hvalid a f)
        (blockRightHistory sources seed V l p b hvalid a' g)
        ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q) := rfl

theorem decoded_updated_smallSourceSamples (giants : Bool → PrimeSource) (q : Block p)
    (x : PairKey (blockLeftHistory sources seed V l p b hvalid a f)
      (blockRightHistory sources seed V l p b hvalid a' g) → ℤ) (n : ℕ)
    (hx : (∏ j, dummyMass giants (decodedRootSources sources seed V l p b hvalid a f)
      sources (pairedInternalOrigin seed l) p
      (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q j (x j)) ≠ 0)
    (hn : blockNaturalWeight sources (pairedInternalOrigin seed l) p q n ≠ 0) :
    SmallSourceSamples sources (blockLeftHistory sources seed V l p b hvalid a f)
      (blockRightHistory sources seed V l p b hvalid a' g)
      (Function.update x
        (representativeMap (blockLeftHistory sources seed V l p b hvalid a f)
          (blockRightHistory sources seed V l p b hvalid a' g)
          ((decodedRepresentativeBlockEquiv sources seed V l p b hvalid a a' f g ha ha').symm q))
        (n : ℤ)) := by
  have hp := updated_small_source_values giants
    (decodedRootSources sources seed V l p b hvalid a f)
    sources (pairedInternalOrigin seed l) p
    (decodedSourceEquiv sources seed V l p b hvalid a a' f g ha ha' hs hperm) q x n hx hn
  have ht := smallSourceSamples_of_pattern_values sources seed
    (blockLeftHistory sources seed V l p b hvalid a f)
    (blockRightHistory sources seed V l p b hvalid a' g)
    (blockLeftLabels sources seed V l p b hvalid a f ha)
    (blockRightLabels sources seed V l p b hvalid a' g ha')
    p (natBlockDraw p b Subtype.val Subtype.val_injective)
    (decoded_pair_slot_eq sources seed V l p b hvalid a a' f g ha ha') hs
    (by simpa only [blockLeftHistory,blockRightHistory,decodeHistory_root] using hperm)
    _ hp.1 hp.2
  exact ht

end Decoded
end Ostmann.Arithmetic.HistoryPairSourceLaws

end

end OAI
