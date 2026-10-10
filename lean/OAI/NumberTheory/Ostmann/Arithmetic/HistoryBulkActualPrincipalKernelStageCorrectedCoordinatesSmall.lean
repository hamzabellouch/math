import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedCoordinatesRepresentative

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
local instance correctedKernelCoordinatesSmallInternalDecidable (seed : List SourceSlot) (l : ℕ) :
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

open HistoryBulkFibreOriginalReference
open HistoryPairPattern HistoryPairBulkCoordinates HistoryPairRepresentativeVariables HistoryPairBulkTransport
open HistoryPairKernelReplacement HistoryPairKernelProductReplacement
open HistoryBulkPrincipalKernelReplacementMatched HistoryBulkPrincipalBSquareReference
open HistoryBulkReferenceTests HistoryBulkReferenceScalarCoordinates
open HistoryCompensationRepresentativePatterns HistoryOccurrenceVariables

theorem fixedB_eq_restored_referenceSample_small (u : SelectedBulkSample C l)
    (j : PairKey (R.blockReference (l:=l) he).left.history (R.blockReference (l:=l) he).right.history)
    (hj : ∃a:ℕ×ℤ,j.val=Sum.inr a) :
    (R.frame (l:=l) he hprime).fixedB (fibreAssignment C (outerNonbulk C l p o) u) j=
      referenceSample (C:=C) (l:=l) (R.blockReference (l:=l) he) (restoreOriginalDraw C l p o u) j := by
  obtain ⟨q,rfl⟩ := (typedSourceEquivMatched (R.blockReference (l:=l) he).left (R.blockReference (l:=l) he).right p
    (R.blockReference (l:=l) he).natDraw (R.blockReference (l:=l) he).slot_values (R.blockReference (l:=l) he).root_matching).surjective j
  rcases q with t | j | q
  · rcases hj with ⟨a,ha⟩
    cases ha
  · rw [typedSourceEquivMatched_root]
    refine (R.fixedB_root he hprime u j).trans ?_
    rw [←typedSourceEquivMatched_root (R.blockReference (l:=l) he).left (R.blockReference (l:=l) he).right p
      (R.blockReference (l:=l) he).natDraw (R.blockReference (l:=l) he).slot_values (R.blockReference (l:=l) he).root_matching j]
    simp only [referenceSample,Function.comp_apply,Equiv.symm_apply_apply]
    rfl
  · rw [typedSourceEquivMatched_block]
    exact (fixedB_representative (R.frame (l:=l) he hprime) _ _).trans
      (R.restored_referenceSample_representative he u _).symm

end CorrectedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
