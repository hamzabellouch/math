import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentSelectedPrimeAbsent
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentSelectedPrimeBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentSelectedPrimePattern
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentSelectedPrimeSum

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

theorem selectedPrimeFamily_value_eq_plainPattern :
    @SymbolicPatternFamily.value d Bs BD Bz k L E C (spectatorList spectator ds) l p
      (selectedFamily C (spectatorList spectator ds) hactual hl hout p o false)
      b false (bulkSize k L/2) (fun q hq=>spectator.prime q (hout q hq)) hV =
    @HistoryBulkPatternIntegralReplacement.familyValue d Bs BD Bz L k l E
      C (spectatorList spectator ds) p true
      (HistoryBulkActualGoodPrincipal.plainPatternFamily C spectator ds hactual hl
        (Equiv.refl _) false p o) b false false hV := by
  cases hD : outerData? C p o with
  | none =>
    rw [selectedFamily_eq_empty_of_none C (spectatorList spectator ds) hactual hl hout p o false hD,
      emptyFamily_value]
    exact (prime_plainPattern_value_eq_zero_of_none C spectator ds hactual hl p o b hV hD).symm
  | some D =>
    rw [selectedFamily_prime_eq_of_some C (spectatorList spectator ds) hactual hl hout p o D hD]
    exact (prime_symbolic_value_eq_matched C spectator ds hactual hl hout p o b hV D hD).trans
      (prime_plainPattern_value_eq_matched C spectator ds hactual hl p o b hV).symm

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
