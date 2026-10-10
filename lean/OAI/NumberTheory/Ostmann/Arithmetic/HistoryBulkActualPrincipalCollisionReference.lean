import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorReferences

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation HistoryBulkFibreOriginalReference
open HistoryBulkPrincipalCollisionError
attribute [local instance] Classical.propDecidable
local instance actualCollisionInternalDecidable (seed : List SourceSlot) (l : ℕ) :
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
  (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

def collisionReference : PrincipalCollisionReference C outside (outerNonbulk C l p o) p where
  amplitude := (R.principalData hcell (bulkSize k L/2) hlen hp hV true).amplitude R.witness.bulk
  referenceBulk := R.witness.bulk
  leftSmall := by
    change R.blockReference.left.history.root.small = _
    rw [R.blockReference.left_root]
    rfl
  representative := R.representative hcell hp
  residues u := (R.principalData hcell (bulkSize k L/2) hlen hp hV true).amplitude u |>.residue

@[simp] theorem collisionReference_value (corrected mixed : Bool) (u : SelectedBulkSample C l) :
    (R.collisionReference hcell hlen hp hV).value corrected mixed u =
      (R.principalData hcell (bulkSize k L/2) hlen hp hV true).value corrected mixed u := rfl

@[simp] theorem collisionReference_left :
    (R.collisionReference hcell hlen hp hV).amplitude.left=(R.frame hcell hp).left := rfl
@[simp] theorem collisionReference_right :
    (R.collisionReference hcell hlen hp hV).amplitude.right=(R.frame hcell hp).right := rfl

end MatchedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
