import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterBackgroundDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexMatchedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacementDensityBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamily
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantApproximation HistoryBulkFibreOriginalReference
open HistoryBulkPrincipalBSquareReplacement HistoryRepresentativeSourceSeparation
open HistoryBulkReferencePeriodicMeanSource
attribute [local instance] Classical.propDecidable
local instance reindexFamilyDefsInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
    SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
  (hw : ∀r,0≤w r) (hpos : ∀r,w r≠0 → 0<P r ∧ 0<Q r)
  (hcell : ∀r,w r≠0 → 0<P r ∧ 0<Q r ∧
    |Real.log (P r:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q r:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hp : ∀q∈outside,q.Prime)
  (hAd : ∀r : Frame (l:=l) C outside, PairAdmissible r.left r.right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (bg : Background C l) (u : SelectedBulkSample C l)
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))

def selectedOuter
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :=
  selectMatchedOuterReference C p (restoreOuterBackground C l p bg b)
    outside σ J w P Q i hactual hl houtside hw hpos

def referenceFamily : ReferenceFamily C outside l := fun p b=>
  if hu : (selectedBulkPrior C l).mass u≠0 then
    (selectedOuter C outside σ J w P Q hactual hl houtside hw hpos bg i p b).map
      (fun R=>R.squareReference (l:=l) hcell hp (hAd (R.frame (l:=l) hcell hp))
        hout hV u hu)
  else none

def densitySources : DensitySources C l := fun p b=>
  (selectedOuter C outside σ J w P Q hactual hl houtside hw hpos bg i p b).elim
    (fibreAssignment C bg.2 u) (fun R=>(R.frame (l:=l) hcell hp).leftSource)

def staticCondition (r : Frame (l:=l) C outside) : Prop :=
  let x := fibreAssignment C bg.2 u
  let y := permuteAssignment C σ x
  (((r.newLeft x).root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime ∧
    ((r.newRight y).root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime)

def staticMask
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) : Prop :=
  (selectedBulkPrior C l).mass u≠0 ∧
    (selectedOuter C outside σ J w P Q hactual hl houtside hw hpos bg i p b).elim
      False (fun R=>staticCondition C outside σ bg u (R.frame (l:=l) hcell hp))

def expression (probability corrected mixed : Bool) : ℂ :=
  densityBExpressionSum
    (referenceFamily C outside σ J w P Q hactual hl houtside hw hpos hcell hp hAd hout hV bg u i)
    (densitySources C outside σ J w P Q hactual hl houtside hw hpos hcell hp bg u i)
    probability corrected mixed
    (staticMask C outside σ J w P Q hactual hl houtside hw hpos hcell hp bg u i)

def rootExpression (probability corrected mixed : Bool) : ℂ :=
  ∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
    expression C outside σ J w P Q hactual hl houtside hw hpos hcell hp hAd hout hV bg u i
      probability corrected mixed

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamily

end

end OAI
