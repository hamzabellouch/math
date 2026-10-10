import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalDensity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterBackgroundDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorActualDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkPrincipalCollisionError HistoryBulkActualGoodPrincipal
attribute [local instance] Classical.propDecidable
local instance selectedCollisionInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
  (hw : ∀r,0≤w r) (hpos : ∀r,w r≠0 → 0<P r ∧ 0<Q r)
  (hcell : ∀r,w r≠0 → 0<P r ∧ 0<Q r ∧
    |Real.log (P r:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q r:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (bg : Background C l)
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))

def selectedCollisionReferences
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    Option (PrincipalCollisionReference C outside bg.2 p) :=
  (selectMatchedOuterReference C p (restoreOuterBackground C l p bg b) outside σ J w P Q i
    hactual hl houtside hw hpos).map (fun R=>R.collisionReference hcell hlen hp hV)

def selectedCollisionMask (mixed : Bool) (_u : SelectedBulkSample C l)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) : ℝ :=
  (selectMatchedOuterReference C p (restoreOuterBackground C l p bg b) outside σ J w P Q i
    hactual hl houtside hw hpos).elim 0 (fun R=>density (R.frame hcell hp) mixed)

theorem selectedCollisionMask_mem (mixed : Bool) (u : SelectedBulkSample C l) (p) (b) :
    0 ≤ selectedCollisionMask C outside σ J w P Q hactual hl houtside hw hpos hcell hp bg i mixed u p b ∧
    selectedCollisionMask C outside σ J w P Q hactual hl houtside hw hpos hcell hp bg i mixed u p b ≤ 1 := by
  unfold selectedCollisionMask
  cases hr : selectMatchedOuterReference C p (restoreOuterBackground C l p bg b) outside σ J w P Q i
      hactual hl houtside hw hpos with
  | none => exact ⟨le_rfl,zero_le_one⟩
  | some R => exact density_mem (R.frame hcell hp) mixed

def selectedCollisionMean (corrected mixed guarded : Bool) : ℂ :=
  ∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
    collisionPrincipalMean C
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
      outside bg.2
      (selectedCollisionReferences C outside σ J w P Q hactual hl houtside hw hpos hcell hlen hp hV bg i)
      (selectedCollisionMask C outside σ J w P Q hactual hl houtside hw hpos hcell hp bg i mixed)
      corrected mixed guarded

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
