import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexPrimeLaw
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexRawPrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexSpectator

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

theorem original_prime_principal_eq_B_sourceMean
    (hAd : ∀ds : Fin (2*(bulkSize k L/2))→spectator.Sample,
      ∀r : Frame (l:=l) C (spectatorList spectator ds),
        PairAdmissible r.left r.right (spectatorList spectator ds))
    (hV : ∀ds : Fin (2*(bulkSize k L/2))→spectator.Sample,
      ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q)
    (hfreq : ∀_ : Fin (2*(bulkSize k L/2))→spectator.Sample,∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j)) :
    originalSourceAverage C spectator (primeSelectedPrincipal (l:=l) C spectator hactual hl σ)=
      (spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds=>
        primeSourceMean (l:=l) C (spectatorList spectator ds) σ hactual hl
          (spectatorList_source spectator ds)
          (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
          (hAd ds) (spectatorList_length_eq spectator ds) (hV ds) false) :=
  (original_prime_principal_eq_rawSourceMean (l:=l) C spectator hactual hl σ).trans
    (FinitePrior.cmean_congr_support (spectatorPrior spectator (2*(bulkSize k L/2))) _ _
      (fun ds _=>rawPrimeSourceMean_eq_primeSourceMean (l:=l)
        C (spectatorList spectator ds) σ hactual hl (spectatorList_source spectator ds)
        (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
        (hAd ds) (spectatorList_length_eq spectator ds) (hV ds) (hfreq ds)))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex

end

end OAI
