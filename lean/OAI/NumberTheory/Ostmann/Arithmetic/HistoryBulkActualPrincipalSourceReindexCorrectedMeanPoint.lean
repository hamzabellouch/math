import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexCorrectedMeanDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexCorrectedMeanOption
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyCorrectedFactors

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
local instance correctedRawSourceMeanPointInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands _ e) (hp : ∀q∈outside,q.Prime)
  (hAd : ∀r : Frame (l:=l) C outside, PairAdmissible r.left r.right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

open HistoryBulkUniversalPatternAggregation

variable (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j))
include hfreq

theorem corrected_raw_option_cmean_eq_densityFactor (bg : Background C l)
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    (selectedOuter (l:=l) C outside e bg i p b).elim 0
      (fun R=>(selectedBulkPrior C l).cmean (R.rawBTerm (l:=l) he hp))=
    (selectedBulkPrior C l).cmean (fun u=>densityPatternFactor
      (referenceFamily (l:=l) C outside e he hp hAd hout hV bg u i)
      (densitySources (l:=l) C outside e he hp bg u i) false true true
      (staticMask (l:=l) C outside e he hp bg u i) p b) := by
  refine (raw_option_cmean_eq_square (l:=l) C outside e he hp hAd hout hV hfreq bg i p b).trans ?_
  apply congrArg (selectedBulkPrior C l).cmean
  funext u
  exact (HistoryBulkActualPrincipalSourceReindexFamilyCorrected.densityPatternFactor_false_eq
    (l:=l) C outside e he hp hAd hout hV bg u i p b).symm

end Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement

end

end OAI
