import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalCorrectedReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexSquare
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMixedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferenceMatched
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacementFinite

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation
open HistoryBulkFibreOriginalReference HistoryBulkIndependentFibreReference
open HistoryBulkFibreGiantApproximationReference HistoryPairRepresentatives
open HistoryPairReferenceSourceTransport HistoryBulkActualPrincipalBlockFamily
open HistoryBulkPrincipalBSquareReference HistoryBulkPrincipalBSquareReplacement
open HistoryBulkActualPrincipalSourceReindex HistoryRepresentativeSourceSeparation
open HistoryBulkReferencePeriodicMeanSource CanonicalHistoryLeafBulk
attribute [local instance] Classical.propDecidable
local instance correctedSquareSourceInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ}{e : RemainingPermutation (k:=k) (L:=L) (l:=l)}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}
namespace CorrectedSelectedOuter
variable (R : CorrectedSelectedOuter C p o outside e i)
  (he : PreservesRemainingBands _ e) (hprime : ∀q∈outside,q.Prime)

def squareRightSource (u : SelectedBulkSample C l) : Frame.Source (C:=C) (l:=l) :=
  rightAssignment C (outerNonbulk C l p o) e u
    (reference_compatible_all C outside (outerNonbulk C l p o) e he i.1.val i.1.val
      (leftChoices C (leftBlockDraws C p R.data.blockDraw R.data.valid) i)
      (rightChoices C (rightBlockDraws C p R.data.blockDraw R.data.valid) i) R.witness u)

theorem squareSource_mass (R : CorrectedSelectedOuter C p o outside e i) (u : SelectedBulkSample C l)
    (hu : (selectedBulkPrior C l).mass u≠0) :
    (assignmentPrior C.sources _).mass (fibreAssignment C (outerNonbulk C l p o) u)≠0 :=
  (fibreAssignment_mass_pos C _ u R.data.nonbulk_pos
    (lt_of_le_of_ne ((selectedBulkPrior C l).mass_nonneg u) (Ne.symm hu))).ne'

variable (had : PairAdmissible (R.frame he hprime).left (R.frame he hprime).right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

def squareReference (u : SelectedBulkSample C l) (hu : (selectedBulkPrior C l).mass u≠0) :
    PrincipalSquareReference C outside l p (outerBlocks C l p o) :=
  principalSquareReference_of_matchedBlockReference (l:=l) (R.frame he hprime) (R.blockReference he) rfl rfl
    (fibreAssignment C (outerNonbulk C l p o) u) (R.squareSource_mass u hu) had
    (bulkSize k L/2) hout hV R.permutation k

def rawBTerm (u : SelectedBulkSample C l) : ℂ :=
  let f := R.frame he hprime
  let x := fibreAssignment C (outerNonbulk C l p o) u
  let y := R.squareRightSource he u
  staticPairMask (f.newLeft x) (f.newRight y) outside*
    f.principalCorrectedMixed R.permutation x y

def squareBTerm (u : SelectedBulkSample C l) : ℂ :=
  if hu : (selectedBulkPrior C l).mass u≠0 then
    let f := R.frame he hprime
    let x := fibreAssignment C (outerNonbulk C l p o) u
    let y := R.squareRightSource he u
    let S := R.squareReference he hprime had hout hV u hu
    staticPairMask (f.newLeft x) (f.newRight y) outside *
      (Frame.extractedDensity (C:=C) f.leftSource *
        (S.principal.value true true S.newBulk*bMean S true))
  else 0

end CorrectedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
