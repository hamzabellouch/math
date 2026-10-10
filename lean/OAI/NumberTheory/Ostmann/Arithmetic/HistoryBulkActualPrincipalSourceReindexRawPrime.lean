import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexBackgroundRoot
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexMeanDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionPrime

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

theorem original_prime_principal_eq_rawSourceMean :
    originalSourceAverage C spectator (primeSelectedPrincipal (l:=l) C spectator hactual hl σ)=
      (spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds=>
        rawSourceMean (l:=l) C (spectatorList spectator ds) σ (primeLawMultiplier (l:=l) C)
          (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) hactual hl
          (spectatorList_source spectator ds) (primeWeight_nonneg C.giant)
          (fun r _=>primeDraw_positive C.giant r)
          (fun r hr=>prime_draw_cells C r
            (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr)))
          (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) false false) :=
  (originalSourceAverage_eq_backgroundPatternMean (l:=l) C spectator
    (primeSelectedPrincipal (l:=l) C spectator hactual hl σ)).trans
    (FinitePrior.cmean_congr_support (spectatorPrior spectator (2*(bulkSize k L/2))) _ _
      (fun ds _=>background_pattern_root_congr (l:=l) C _ _
        (fun bg i p b ho ht=>prime_patternValue_eq_rawOption (l:=l)
          C p (restoreOuterBackground C l p bg b) spectator hactual hl σ ds i ho ht)))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex

end

end OAI
