import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexMatchedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionAlgebra

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily HistoryBulkReferenceFrequencyFamily
open HistoryBulkFibreGiantErrorAverage HistoryBulkPrincipalSourceReindexWitness
open HistoryBulkActualPrincipalBlockFamily HistoryPairReferenceFlagExpectation
open HistoryBulkActualPrincipalSourceReindexPattern HistoryBulkActualPrincipalSourceReindexCompensation
open HistoryGiantReferenceMean HistoryBulkFibreGiantApproximationReference
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)

variable (spectator : PrimeSource)
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
  (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
  (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l)

def mixedRawOption : ℂ :=
  (selectMatchedOuterReference C p o (spectatorList spectator ds) σ (fun i=>plainMixedWeight C (spectatorList spectator ds) (outerNonbulk C l p o) i.1.val)
    (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i hactual hl
    (spectatorList_source spectator ds) (mixedWeight_nonneg C.giantCenter C.giant)
    (fun r _=>mixedDraw_positive C.giantCenter C.giant r)).elim 0 (fun R=>
      (selectedBulkPrior C l).cmean (R.rawBTerm
        (fun v hv=>mixed_draw_cells C v (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant v) (Ne.symm hv)))
        (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) false true))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

end

end OAI
