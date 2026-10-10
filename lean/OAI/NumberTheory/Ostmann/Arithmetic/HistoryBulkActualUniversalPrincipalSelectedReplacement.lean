import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalReplacementFamily
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalSelectedProperties
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPatternIntegralReplacementBackground

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkSourceDisintegration
open HistoryBulkUniversalPatternAggregation HistoryBulkActualPrincipalBlockFamily
open HistoryBulkReferenceFrequencyFamily
attribute [local instance] Classical.propDecidable
local instance universalPrincipalSelectedReplacementInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (hout : ∀q∈outside,q∈spectator.candidates)

def selectedReplacementBackground :
    Background C l → ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      (Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) →
      Bool → HistoryBulkPatternIntegralReplacement.Family C outside l p :=
  fun bg p b mixed=>replacementFamily
    (selectedFamily C outside hactual hl hout p (restoreOuterBackground C l p bg b) mixed)
    (fun q hq=>spectator.prime q (hout q hq))

theorem selectedAggregate_eq_replacementBackground (mixed : Bool)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    selectedAggregate C outside hactual hl hout mixed hV =
      HistoryBulkPatternIntegralReplacement.backgroundValue true
        (fun bg p b=>selectedReplacementBackground C outside hactual hl hout bg p b mixed)
        false mixed hV := by
  rw [selectedAggregate_eq_background]
  unfold HistoryBulkPatternIntegralReplacement.backgroundValue
  apply congrArg (backgroundPrior C l).cmean
  funext bg
  unfold patternComplexSum
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · congr 1
    symm
    exact familyValue_replacementFamily _ _
      (selectedFamily_permutation C outside hactual hl hout p _ mixed) mixed
      (selectedFamily_mask C outside hactual hl hout p _ mixed) b hV
  · rfl

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
