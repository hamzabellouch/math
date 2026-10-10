import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementCorrectedBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexCorrectedMeanBackground
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexCorrectedMeanDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexExchange

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantApproximation HistoryBulkFibreOriginalReference
open HistoryBulkPrincipalBSquareReplacement HistoryRepresentativeSourceSeparation
open HistoryBulkReferenceFrequencyFamily
open HistoryBulkActualPrincipalSourceReindexFamilyCorrected
open HistoryBulkIndependentFibreReference
attribute [local instance] Classical.propDecidable
local instance correctedRawSourceMeanFinalInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands _ e) (hp : ∀q∈outside,q.Prime)
  (hAd : ∀r : Frame (l:=l) C outside, PairAdmissible r.left r.right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

open HistoryBulkUniversalPatternAggregation

open HistoryBulkActualPrincipalSourceReindex
variable (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j))
include hfreq

theorem correctedRawSourceMean_eq_correctedSourceMean :
    correctedRawSourceMean (l:=l) C outside e he hp=
      correctedSourceMean (l:=l) C outside e he hp hAd hout hV false := by
  unfold correctedRawSourceMean correctedSourceMean
  apply congrArg (backgroundPrior C l).cmean
  funext bg
  exact correctedRawSourceBackground_eq (l:=l) C outside e he hp hAd hout hV hfreq bg

end Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement

end

end OAI
