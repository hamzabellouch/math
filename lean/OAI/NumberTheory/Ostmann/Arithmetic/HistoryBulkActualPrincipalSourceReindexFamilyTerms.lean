import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyDefs

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

variable (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : Block p → CommonSample C.sources
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))

def squareTerm (R : MatchedSelectedOuter C p (restoreOuterBackground C l p bg b)
    outside σ J w P Q i) (probability corrected mixed : Bool) : ℂ :=
  if hu : (selectedBulkPrior C l).mass u≠0 then
    let f := R.frame (l:=l) hcell hp
    let x := fibreAssignment C bg.2 u
    let y := permuteAssignment C σ x
    let S := R.squareReference (l:=l) hcell hp (hAd f) hout hV u hu
    staticPairMask (f.newLeft x) (f.newRight y) outside *
      ((if mixed then Frame.extractedDensity (C:=C) f.leftSource else 1)*
        (S.principal.value corrected mixed S.newBulk *
          (if probability then probabilityProduct S mixed else bMean S mixed)))
  else 0

def selectedTerm (probability corrected mixed : Bool) : ℂ :=
  (selectedOuter C outside σ J w P Q hactual hl houtside hw hpos bg i p b).elim 0
    (fun R=>squareTerm C outside σ J w P Q hcell hp hAd hout hV bg u i p b R
      probability corrected mixed)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamily

end

end OAI
