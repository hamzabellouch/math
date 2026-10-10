import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalPlainDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalDefs

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
  (mixed : Bool)
  (b : Block p → CommonSample C.sources
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
  (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q)

def SelectedAlignment : Prop :=
    @SymbolicPatternFamily.value d Bs BD Bz k L E C (spectatorList spectator ds) l p
      (@selectedFamily d Bs BD Bz L k l E C (spectatorList spectator ds) spectator hactual hl hout p o mixed)
      b mixed (bulkSize k L/2) (fun q hq=>spectator.prime q (hout q hq)) hV =
    @HistoryBulkPatternIntegralReplacement.familyValue d Bs BD Bz L k l E C
      (spectatorList spectator ds) p true
      (@HistoryBulkActualGoodPrincipal.plainPatternFamily d Bs BD Bz L k l E C spectator ds hactual hl
        (Equiv.refl _) mixed p o) b false mixed hV

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
