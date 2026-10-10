import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexCorrected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexExchange
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyCorrectedDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantApproximation HistoryBulkFibreOriginalReference
open HistoryBulkPrincipalBSquareReplacement HistoryRepresentativeSourceSeparation
open HistoryBulkActualPrincipalSourceReindex
open HistoryBulkActualPrincipalSourceReindexFamilyCorrected
open HistoryBulkIndependentFibreReference HistoryBulkActualGoodPrincipal
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands _ e) (hp : ∀q∈outside,q.Prime)
  (hAd : ∀r : Frame (l:=l) C outside, PairAdmissible r.left r.right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j))
  (bg : Background C l)
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : Block p → CommonSample C.sources
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
include hfreq

theorem raw_option_cmean_eq_square :
    (selectedOuter (l:=l) C outside e bg i p b).elim 0
      (fun R=>(selectedBulkPrior C l).cmean (R.rawBTerm (l:=l) he hp))=
    (selectedBulkPrior C l).cmean
      (fun u=>(selectedOuter (l:=l) C outside e bg i p b).elim 0
        (fun R=>R.squareBTerm (l:=l) he hp (hAd (R.frame (l:=l) he hp)) hout hV u)) := by
  have hmean := fun R : CorrectedSelectedOuter C p
      (restoreOuterBackground C l p bg b) outside e i =>
    R.mean_rawBTerm_eq_squareBTerm (l:=l) he hp
      (hAd (R.frame (l:=l) he hp)) hout hV hfreq
  exact (congrArg ((selectedOuter (l:=l) C outside e bg i p b).elim (0:ℂ))
    (funext hmean)).trans
      (option_cmean (selectedBulkPrior C l)
        (selectedOuter (l:=l) C outside e bg i p b)
        (fun R=>R.squareBTerm (l:=l) he hp
          (hAd (R.frame (l:=l) he hp)) hout hV))

end Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement

end

end OAI
