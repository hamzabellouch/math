import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMixedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferenceMatched
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacementFinite

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation
open HistoryBulkFibreOriginalReference
open HistoryBulkFibreGiantApproximationReference HistoryPairRepresentatives
open HistoryPairReferenceSourceTransport
attribute [local instance] Classical.propDecidable
local instance actualSquareSourceInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ}
  {σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))}
  {J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ}
  {α : Type} [Fintype α] {w : α→ℝ} {P Q : α→ℤ}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}

namespace MatchedSelectedOuter
variable (R : MatchedSelectedOuter C p o outside σ J w P Q i)
  (hcell : ∀v,w v≠0 → 0<P v ∧ 0<Q v ∧
    |Real.log (P v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q v:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hprime : ∀q∈outside,q.Prime)

open HistoryBulkPrincipalBSquareReference HistoryBulkPrincipalBSquareReplacement
open HistoryRepresentativeSourceSeparation
open HistoryBulkReferencePeriodicMeanSource CanonicalHistoryLeafBulk
variable (had : PairAdmissible (R.frame (l:=l) hcell hprime).left (R.frame (l:=l) hcell hprime).right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem squareSource_mass (R : MatchedSelectedOuter C p o outside σ J w P Q i) (u : SelectedBulkSample C l)
    (hu : (selectedBulkPrior C l).mass u≠0) :
    (assignmentPrior C.sources _).mass (fibreAssignment C (outerNonbulk C l p o) u)≠0 :=
  (fibreAssignment_mass_pos (l:=l) C (outerNonbulk C l p o) u R.data.nonbulk_pos
    (lt_of_le_of_ne ((selectedBulkPrior C l).mass_nonneg u) (Ne.symm hu))).ne'

def squareReference (u : SelectedBulkSample C l) (hu : (selectedBulkPrior C l).mass u≠0) :
    PrincipalSquareReference C outside l p (outerBlocks C l p o) :=
  principalSquareReference (l:=l) (R.frame (l:=l) hcell hprime)
    (fibreAssignment C (outerNonbulk C l p o) u) (R.squareSource_mass (l:=l) u hu)
    p R.data.blockDraw (by exact R.blockReference.slot_values) had
    (bulkSize k L/2) hout hV σ k

def rawBTerm (corrected mixed : Bool) (u : SelectedBulkSample C l) : ℂ :=
  let f := R.frame (l:=l) hcell hprime
  let x := fibreAssignment C (outerNonbulk C l p o) u
  let y := permuteAssignment C σ x
  staticPairMask (f.newLeft x) (f.newRight y) outside*
    (if mixed then
      (if corrected then f.principalCorrectedMixed σ x y else f.principalMixed σ x y)
     else f.principal σ x y)

def squareBTerm (corrected mixed : Bool) (u : SelectedBulkSample C l) : ℂ :=
  if hu : (selectedBulkPrior C l).mass u≠0 then
    let f := R.frame (l:=l) hcell hprime
    let x := fibreAssignment C (outerNonbulk C l p o) u
    let y := permuteAssignment C σ x
    let S := R.squareReference (l:=l) hcell hprime had hout hV u hu
    staticPairMask (f.newLeft x) (f.newRight y) outside *
      ((if mixed then Frame.extractedDensity (C:=C) f.leftSource else 1)*
        (S.principal.value corrected mixed S.newBulk*bMean S mixed))
  else 0

end MatchedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
