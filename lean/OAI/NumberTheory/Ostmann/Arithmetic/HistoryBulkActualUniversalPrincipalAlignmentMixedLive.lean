import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentMixedPattern
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentMixedSum
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentSelectedMixedBasic

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

theorem selectedFamily_value_eq_plainPattern_mixed_of_some (D : OuterData C p o)
    (hD : outerData? C p o=some D) :
    @SymbolicPatternFamily.value d Bs BD Bz k L E C (spectatorList spectator ds) l p
      (selectedFamily C (spectatorList spectator ds) hactual hl hout p o true)
      b true (bulkSize k L/2) (fun q hq=>spectator.prime q (hout q hq)) hV =
    @HistoryBulkPatternIntegralReplacement.familyValue d Bs BD Bz L k l E C
      (spectatorList spectator ds) p true
      (HistoryBulkActualGoodPrincipal.plainPatternFamily C spectator ds hactual hl
        (Equiv.refl _) true p o) b false true hV := by
  have he := congrArg
    (fun F : SymbolicPatternFamily C (spectatorList spectator ds) l p =>
      @SymbolicPatternFamily.value d Bs BD Bz k L E C (spectatorList spectator ds) l p
        F b true (bulkSize k L/2) (fun q hq=>spectator.prime q (hout q hq)) hV)
    (selectedFamily_mixed_eq_of_some C spectator ds hactual hl hout p o D hD)
  exact he.trans ((mixed_symbolic_value_eq_matched C spectator ds hactual hl hout p o b hV D hD).trans
    (mixed_matched_value_eq_plainPattern C spectator ds hactual hl p o b hV))

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
