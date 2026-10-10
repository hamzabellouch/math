import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedReferenceFamilyMatchedReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalCorrectedReferenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGoodPatternAggregationReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportBlocks
import OAI.NumberTheory.Ostmann.Construction.DiagonalPermutationCount

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualRootReferenceFamily HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference HistoryBulkFibreGiantApproximation
open HistoryPairRepresentatives HistoryPairReferenceSourceTransport
attribute [local instance] Classical.propDecidable
local instance actualGoodCorrectedReferenceFrameInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ} {e : RemainingPermutation (k:=k) (L:=L) (l:=l)}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}
namespace CorrectedSelectedOuter
variable (R : CorrectedSelectedOuter C p o outside e i)
  (he : PreservesRemainingBands _ e) (hprime : ∀q∈outside,q.Prime)

def blockReference : MatchedBlockReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
    (frequencyBound Bs BD Bz k L) outside l p :=
  HistoryBulkActualCorrectedReferenceFamily.matchedWitnessBlockReference C p
    R.data.blockDraw R.data.valid outside (outerNonbulk C l p o) e
    i.1.val i.1.val i.2.1 i.2.2 R.witness he

def frame : Frame (l:=l) C outside :=
  HistoryBulkActualCorrectedReferenceFamily.witnessFrame C outside
    (outerNonbulk C l p o) e i.1.val i.1.val
    (leftChoices C (leftBlockDraws C p R.data.blockDraw R.data.valid) i)
    (rightChoices C (rightBlockDraws C p R.data.blockDraw R.data.valid) i)
    he R.data.nonbulk_pos (R.data.left_mass i) (R.data.right_mass i) hprime R.witness

@[simp] theorem frame_left : (R.frame he hprime).left=(R.blockReference he).left.history := rfl
@[simp] theorem frame_right : (R.frame he hprime).right=(R.blockReference he).right.history := rfl
@[simp] theorem frame_s : (R.frame he hprime).s=i.1.val := rfl
@[simp] theorem frame_t : (R.frame he hprime).t=i.1.val := rfl

def representative : Block p ≃ Representative (R.frame he hprime).left (R.frame he hprime).right :=
  (typedBlockEquiv (R.blockReference he).left (R.blockReference he).right p
    (R.blockReference he).natDraw (R.blockReference he).slot_values).symm

def permutation (_R : CorrectedSelectedOuter C p o outside e i) : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))) :=
  DiagonalPermutationCount.remainingBulkPermutation (2*(bulkSize k L/2)) k l e

def goodReference (hgood : ¬TransferBadArrangement (R.permutation))
    (mask : ℝ) (hmask : 0 ≤ mask ∧ mask ≤ 1) :
    HistoryBulkGoodPatternAggregation.Reference C outside l p where
  frame := R.frame he hprime
  permutation := R.permutation
  good := hgood
  representative := R.representative he hprime
  mask := mask
  mask_mem := hmask

@[simp] theorem goodReference_frame (hgood : ¬TransferBadArrangement (R.permutation))
    (mask : ℝ) (hmask : 0 ≤ mask ∧ mask ≤ 1) :
    (R.goodReference he hprime hgood mask hmask).frame=R.frame he hprime := rfl

@[simp] theorem goodReference_permutation (hgood : ¬TransferBadArrangement (R.permutation))
    (mask : ℝ) (hmask : 0 ≤ mask ∧ mask ≤ 1) :
    (R.goodReference he hprime hgood mask hmask).permutation=
      DiagonalPermutationCount.remainingBulkPermutation (2*(bulkSize k L/2)) k l e := rfl

end CorrectedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
