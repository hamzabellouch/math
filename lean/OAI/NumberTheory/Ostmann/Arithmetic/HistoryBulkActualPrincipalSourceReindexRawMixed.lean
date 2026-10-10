import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexBackgroundRoot
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexMeanDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationFibreIdentities

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkActualPrincipalBlockFamily HistoryBulkUniversalPatternAggregation
open HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalSourceReindexPattern HistoryBulkFibreGiantErrorAverage
open HistoryBulkReferenceFrequencyFamily HistoryPairSourceLaws
open HistoryBulkActualBSquareReplacement HistoryBulkActualPrincipalSourceReindexFamily
open HistoryBulkActualPrincipalSourceReindexOption HistoryGiantReferenceMean
open HistoryBulkFibreGiantApproximationReference HistoryBulkFibreGiantApproximation
open HistoryRepresentativeSourceSeparation
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))

theorem original_mixed_principal_eq_rawSourceMean :
    originalSourceAverage C spectator (mixedSelectedPrincipal (l:=l) C spectator hactual hl σ)=
      (spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds=>
        rawSourceMean (l:=l) C (spectatorList spectator ds) σ (plainMixedLawMultiplier (l:=l) C (spectatorList spectator ds))
          (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) hactual hl
          (spectatorList_source spectator ds) (mixedWeight_nonneg C.giantCenter C.giant)
          (fun r _=>mixedDraw_positive C.giantCenter C.giant r)
          (fun r hr=>mixed_draw_cells C r
            (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr)))
          (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) false true) :=
  (originalSourceAverage_eq_backgroundPatternMean (l:=l) C spectator
    (mixedSelectedPrincipal (l:=l) C spectator hactual hl σ)).trans
    (FinitePrior.cmean_congr_support (spectatorPrior spectator (2*(bulkSize k L/2))) _ _
      (fun ds _=>background_pattern_root_congr (l:=l) C _ _
        (fun bg i p b ho ht=>mixed_patternValue_eq_rawOption (l:=l)
          C p (restoreOuterBackground C l p bg b) spectator hactual hl σ ds i ho ht)))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex

end

end OAI
