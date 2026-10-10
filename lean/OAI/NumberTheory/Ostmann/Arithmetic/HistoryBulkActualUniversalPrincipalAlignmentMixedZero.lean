import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentMixedAbsent
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentSelectedPrimeBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkSourceDisintegration
open HistoryBulkUniversalPatternAggregation HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualRootReferenceFamily HistoryBulkFibreGiantApproximation
open HistoryGiantReferenceMean HistoryBulkFibreOriginalReference
open HistoryBulkFibreGiantApproximationReference HistoryBulkFibreGiantErrorAverage
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k)
  (hout : ∀q∈spectatorList spectator ds,q∈spectator.candidates)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources
    (Template.initial (2*(bulkSize k L/2)) k) l p)
  (b : Block p → CommonSample C.sources
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
  (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem selectedFamily_value_eq_plainPattern_mixed_of_none (hD : outerData? C p o=none) :
    @SymbolicPatternFamily.value d Bs BD Bz k L E C (spectatorList spectator ds) l p
      (selectedFamily C (spectatorList spectator ds) hactual hl hout p o true)
      b true (bulkSize k L/2) (fun q hq=>spectator.prime q (hout q hq)) hV =
    @HistoryBulkPatternIntegralReplacement.familyValue d Bs BD Bz L k l E C
      (spectatorList spectator ds) p true
      (HistoryBulkActualGoodPrincipal.plainPatternFamily C spectator ds hactual hl
        (Equiv.refl _) true p o) b false true hV := by
  rw [selectedFamily_eq_empty_of_none C (spectatorList spectator ds) hactual hl hout p o true hD,
    emptyFamily_value]
  exact (mixed_pattern_value_eq_zero_of_none C spectator ds hactual hl p o b hV hD).symm

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
