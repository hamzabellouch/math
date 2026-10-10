import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyMatchedSelectedData
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGoodPatternAggregationReference

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
local instance actualGoodPrincipalReferenceInternalDecidable (seed : List SourceSlot) (l : ℕ) :
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

def frame : Frame (l:=l) C outside :=
  let hm := plain_reference_masses C σ (outerNonbulk C l p o) R.witness.bulk
    R.data.nonbulk_pos R.witness.bulk_pos
  let hg := hcell R.witness.giant R.witness.giant_pos.ne'
  { leftSource := fibreAssignment C (outerNonbulk C l p o) R.witness.bulk
    rightSource := permuteAssignment C σ (fibreAssignment C (outerNonbulk C l p o) R.witness.bulk)
    s := i.1.val
    t := i.1.val
    P := P R.witness.giant
    Q := Q R.witness.giant
    leftChoices := leftChoices C (leftBlockDraws C p R.data.blockDraw R.data.valid) i
    rightChoices := rightChoices C (rightBlockDraws C p R.data.blockDraw R.data.valid) i
    left_mass := hm.1
    right_mass := hm.2
    left_choices_mass := R.data.left_mass i
    right_choices_mass := R.data.right_mass i
    plus_pos := hg.1
    minus_pos := hg.2.1
    plus_cell := hg.2.2.1
    minus_cell := hg.2.2.2
    left_supported := R.witness.supported.1
    right_supported := R.witness.supported.2
    matching := R.blockReference.root_matching
    outside_primes := hprime }

@[simp] theorem frame_left : (R.frame hcell hprime).left=R.blockReference.left.history := rfl

@[simp] theorem frame_right : (R.frame hcell hprime).right=R.blockReference.right.history := rfl

@[simp] theorem frame_leftSource : (R.frame hcell hprime).leftSource=
    fibreAssignment C (outerNonbulk C l p o) R.witness.bulk := rfl

@[simp] theorem frame_rightSource : (R.frame hcell hprime).rightSource=
    permuteAssignment C σ (fibreAssignment C (outerNonbulk C l p o) R.witness.bulk) := rfl

def representative : Block p ≃ Representative (R.frame hcell hprime).left (R.frame hcell hprime).right :=
  (typedBlockEquiv R.blockReference.left R.blockReference.right p
    R.blockReference.natDraw R.blockReference.slot_values).symm

def goodReference (hgood : ¬TransferBadArrangement σ) (mask : ℝ) (hmask : 0 ≤ mask ∧ mask ≤ 1) :
    HistoryBulkGoodPatternAggregation.Reference C outside l p where
  frame := R.frame hcell hprime
  permutation := σ
  good := hgood
  representative := R.representative hcell hprime
  mask := mask
  mask_mem := hmask

@[simp] theorem goodReference_frame (hgood : ¬TransferBadArrangement σ) (mask : ℝ)
    (hmask : 0 ≤ mask ∧ mask ≤ 1) :
    (R.goodReference hcell hprime hgood mask hmask).frame=R.frame hcell hprime := rfl

end MatchedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
