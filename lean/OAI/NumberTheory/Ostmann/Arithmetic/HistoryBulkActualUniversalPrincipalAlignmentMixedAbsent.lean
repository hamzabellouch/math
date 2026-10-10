import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalPlainDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentAbsent

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

theorem mixed_pattern_value_eq_zero_of_none (hD : outerData? C p o=none) :
    @HistoryBulkPatternIntegralReplacement.familyValue d Bs BD Bz L k l E C
      (spectatorList spectator ds) p true
      (HistoryBulkActualGoodPrincipal.plainPatternFamily C spectator ds hactual hl
        (Equiv.refl _) true p o) b false true hV = 0 :=
  matched_pattern_value_eq_zero_of_none C p o hD (spectatorList spectator ds)
        (fun i=>plainMixedWeight C (spectatorList spectator ds) (outerNonbulk C l p o) i.1.val)
        (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant)
        hactual hl (spectatorList_source spectator ds) (mixedWeight_nonneg C.giantCenter C.giant)
        (fun r _=>mixedDraw_positive C.giantCenter C.giant r)
        (fun r hr=>mixed_draw_cells C r
          (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr)))
        (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) true b hV

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
