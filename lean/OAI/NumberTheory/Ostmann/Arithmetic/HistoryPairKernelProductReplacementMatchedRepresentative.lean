import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelProductReplacementMatchedOriginalSamples

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairKernelProductReplacement
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairPattern HistoryPairRepresentatives HistoryPairRepresentativeVariables
open HistoryPairReferenceFlagExpectation HistoryPairReferenceSourceTransport
open HistoryCompensationRepresentativePatterns
variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ} {p : Pattern (pairedHistoryType seed l)}

theorem matchedReferenceSample_representative
    (R : MatchedBlockReference sources seed V outside l p)
    (giants : Bool → PrimeSource) (y : OriginalDraw giants sources seed l p)
    (r : Representative R.left.history R.right.history) :
    matchedReferenceSample R giants y (representativeMap R.left.history R.right.history r)=
      ((y (.inr (.inr (typedBlockEquiv R.left R.right p R.natDraw R.slot_values r)))).val:ℤ) := by
  have hk := typedSourceEquivMatched_block R.left R.right p R.natDraw R.slot_values
    R.root_matching (typedBlockEquiv R.left R.right p R.natDraw R.slot_values r)
  rw [Equiv.symm_apply_apply] at hk
  rw [←hk]
  simp only [matchedReferenceSample,Function.comp_apply,Equiv.symm_apply_apply]
  rfl

theorem matchedReference_prime
    (R : MatchedBlockReference sources seed V outside l p)
    (r : Representative R.left.history R.right.history) :
    prime R.left.history R.right.history r=
      (R.blockDraw.val (typedBlockEquiv R.left R.right p R.natDraw R.slot_values r)).val :=
  representativeBlockEquiv_prime seed R.left.history R.right.history R.left.labels R.right.labels
    p R.natDraw R.slot_values r

end Ostmann.Arithmetic.HistoryPairKernelProductReplacement

end

end OAI
