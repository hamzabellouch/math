import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyCorrectedDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyCorrected
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantApproximation HistoryBulkFibreOriginalReference
open HistoryBulkPrincipalBSquareReplacement HistoryRepresentativeSourceSeparation
open HistoryBulkReferencePeriodicMeanSource HistoryBulkActualGoodPrincipal
open HistoryBulkIndependentFibreReference
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands _ e) (hp : ∀q∈outside,q.Prime)
  (hAd : ∀r : Frame (l:=l) C outside, PairAdmissible r.left r.right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (bg : Background C l) (u : SelectedBulkSample C l)
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))

variable (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : Block p → CommonSample C.sources
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))

def squareTerm
    (R : CorrectedSelectedOuter C p (restoreOuterBackground C l p bg b) outside e i)
    (probability : Bool) : ℂ :=
  if hu : (selectedBulkPrior C l).mass u≠0 then
    let f := R.frame (l:=l) he hp
    let x := fibreAssignment C bg.2 u
    let y := R.squareRightSource (l:=l) he u
    let S := R.squareReference (l:=l) he hp (hAd f) hout hV u hu
    staticPairMask (f.newLeft x) (f.newRight y) outside *
      (Frame.extractedDensity (C:=C) f.leftSource *
        (S.principal.value true true S.newBulk *
          (if probability then probabilityProduct S true else bMean S true)))
  else 0

def selectedTerm (probability : Bool) : ℂ :=
  (selectedOuter C outside e bg i p b).elim 0
    (fun R=>squareTerm C outside e he hp hAd hout hV bg u i p b R probability)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyCorrected

end

end OAI
