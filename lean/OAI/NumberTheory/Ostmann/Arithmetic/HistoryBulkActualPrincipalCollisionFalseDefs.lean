import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreIntegralReplacementFrameWeighted

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreIntegralReplacementFrame
open HistoryPairKernelReplacement
attribute [local instance] Classical.propDecidable
attribute [local instance] HistoryBulkActualPrincipalBlockFamily.actualGoodPrincipalReferenceInternalDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _ : Bool=>C.giant) C.sources
    (Template.initial (2*(bulkSize k L/2)) k) l p)
  (outside : List ℕ) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
    SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
  (hw : ∀r,0≤w r) (hpos : ∀r,w r≠0 → 0<P r ∧ 0<Q r)
  (hcell : ∀r,w r≠0 → 0<P r ∧ 0<Q r ∧
    |Real.log (P r:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q r:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hprime : ∀q∈outside,q.Prime) (mixed : Bool)

def selectedBulkFamilyNormal
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (corrected : Bool)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) : ℂ :=
  ∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
    (selectMatchedOuterReference C p o outside σ J w P Q i
      hactual hl houtside hw hpos).elim 0 (fun R=>
        rootDensity (R.frame hcell hprime) mixed *
          ((∏q : Block p,symbolicKernel mixed (R.frame hcell hprime).left (R.frame hcell hprime).right
            (R.frame hcell hprime).left_supported (R.frame hcell hprime).right_supported
            (R.representative hcell hprime q) (b q).val : ℝ):ℂ) *
          bulkMean (R.frame hcell hprime) corrected mixed (outerNonbulk C l p o) σ hV)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
