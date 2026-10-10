import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalPlainDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSelectedDefs

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

theorem prime_plainPattern_value_eq_matched :
    @HistoryBulkPatternIntegralReplacement.familyValue d Bs BD Bz L k l E
      C (spectatorList spectator ds) p true
      (HistoryBulkActualGoodPrincipal.plainPatternFamily C spectator ds hactual hl
        (Equiv.refl _) false p o) b false false hV =
    HistoryBulkActualGoodPrincipal.selectedValue C p o (spectatorList spectator ds)
      (Equiv.refl _) (fun _ _ _ _=>1)
      (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
      hactual hl (spectatorList_source spectator ds) (primeWeight_nonneg C.giant)
      (fun r _=>primeDraw_positive C.giant r)
      (fun r hr=>prime_draw_cells C r
        (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr)))
      (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) false b false hV :=
  HistoryBulkActualGoodPrincipal.pattern_after_eq_selectedValue C p o
    (spectatorList spectator ds) (Equiv.refl _) (fun _ _ _ _=>1)
    (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
    hactual hl (spectatorList_source spectator ds) (primeWeight_nonneg C.giant)
    (fun r _=>primeDraw_positive C.giant r)
    (fun r hr=>prime_draw_cells C r
      (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr)))
    (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) false b false hV

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
