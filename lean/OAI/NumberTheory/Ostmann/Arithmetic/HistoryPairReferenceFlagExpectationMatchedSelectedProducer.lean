import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationMatchedBlocks
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationMatchedReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationSelectedReindex
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportMatchedLaws

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns HistoryCompensationRepresentativePatterns
open HistoryPairReferenceSourceTransport HistoryPairSourceCoordinates Filter
attribute [local instance] Classical.propDecidable
local instance matchedSelectedProducerInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

namespace MatchedBlockReference
variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ→ℕ}
  {outside : List ℕ} {l : ℕ} {p : Pattern (pairedHistoryType seed l)}

def sourceMean (R : MatchedBlockReference sources seed V outside l p) (giants : Bool→PrimeSource) : ℝ :=
  canonicalSourceMeanMatched R.left R.right p R.natDraw R.slot_values R.root_matching giants (family R.left R.right)
end MatchedBlockReference

theorem selected_matched_reference_sourceMean_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀l,l ≤ k → ∀outside : List ℕ,
      ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      ∀R : MatchedBlockReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
        (frequencyBound Bs BD Bz k L) outside l p,
      R.sourceMean (fun _ : Bool=>C.giant) ≤ selectedUnitBudget Bs BD Bz k L R.left.history R.right.history := by
  filter_upwards [selected_canonical_block_family_bound_matched_eventually d Bs BD Bz hk] with L hL
  intro E C hG hGu hc hcu hb hd l hl outside p R
  have h := hL E C hG hGu hc hcu hb hd (2*(bulkSize k L/2)) l hl
    (frequencyBound Bs BD Bz k L) p R.blockDraw R.valid R.leftRoot R.rightRoot
    R.leftFrequency R.rightFrequency R.leftMatch R.rightMatch outside R.leftSupported R.rightSupported R.rootMatching
  have he := selectedUnitBudget_reindex Bs BD Bz k L R.left.history R.right.history
    (decodedRepresentativeBlockEquiv C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) l p R.blockDraw R.valid R.leftRoot R.rightRoot
      R.leftFrequency R.rightFrequency R.leftMatch R.rightMatch)
  exact h.trans_eq he.symm

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
