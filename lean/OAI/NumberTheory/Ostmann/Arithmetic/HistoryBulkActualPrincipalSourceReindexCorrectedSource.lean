import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementCorrectedBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexCorrectedMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexRawCorrected

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
open HistoryBulkActualBSquareReplacement HistoryBulkActualPrincipalSourceReindexFamilyCorrected
open HistoryBulkActualPrincipalSourceReindexOption HistoryGiantReferenceMean
open HistoryBulkFibreGiantApproximationReference HistoryBulkFibreGiantApproximation
open HistoryRepresentativeSourceSeparation
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (e : HistoryBulkIndependentFibreReference.RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands _ e)

theorem original_corrected_principal_eq_B_sourceMean
    (hAd : ∀ds : Fin (2*(bulkSize k L/2))→spectator.Sample,
      ∀r : Frame (l:=l) C (spectatorList spectator ds),
        PairAdmissible r.left r.right (spectatorList spectator ds))
    (hV : ∀ds : Fin (2*(bulkSize k L/2))→spectator.Sample,
      ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q)
    (hfreq : ∀_ : Fin (2*(bulkSize k L/2))→spectator.Sample,∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j)) :
    originalSourceAverage C spectator (correctedSelectedPrincipal (l:=l) C spectator e he)=
      (spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds=>
        @correctedSourceMean d Bs BD Bz L k l E C (spectatorList spectator ds) e he
          (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
          (hAd ds) List.length_ofFn (hV ds) false) :=
  (@original_corrected_principal_eq_rawSourceMean d Bs BD Bz L k l E C spectator e he).trans
    (FinitePrior.cmean_congr_support (spectatorPrior spectator (2*(bulkSize k L/2))) _ _
      (fun ds _=>@correctedRawSourceMean_eq_correctedSourceMean d Bs BD Bz L k l E
        C (spectatorList spectator ds) e he
        (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
        (hAd ds) List.length_ofFn (hV ds) (hfreq ds)))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex

end

end OAI
