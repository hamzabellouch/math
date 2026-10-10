import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCoordinatesRepresentative

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
local instance actualKernelStageCoordinatesSmallInternalDecidable (seed : List SourceSlot) (l : ℕ) :
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

open HistoryPairPattern HistoryPairBulkCoordinates HistoryPairRepresentativeVariables HistoryPairBulkTransport
open HistoryPairKernelReplacement HistoryPairKernelProductReplacement
open HistoryBulkPrincipalKernelReplacementMatched HistoryBulkPrincipalBSquareReference
open HistoryBulkReferenceTests HistoryBulkReferenceScalarCoordinates
open HistoryCompensationRepresentativePatterns HistoryOccurrenceVariables

theorem fixedB_eq_restored_referenceSample_small (u : SelectedBulkSample C l)
    (j : PairKey (R.blockReference (l:=l)).left.history (R.blockReference (l:=l)).right.history)
    (hj : ∃a:ℕ×ℤ,j.val=Sum.inr a) :
    (R.frame (l:=l) hcell hprime).fixedB (fibreAssignment C (outerNonbulk C l p o) u) j=
      referenceSample (C:=C) (l:=l) (R.blockReference (l:=l)) (restoreOriginalDraw C l p o u) j := by
  obtain ⟨q,rfl⟩ := (typedSourceEquivMatched (R.blockReference (l:=l)).left (R.blockReference (l:=l)).right p
    (R.blockReference (l:=l)).natDraw (R.blockReference (l:=l)).slot_values (R.blockReference (l:=l)).root_matching).surjective j
  rcases q with t | j | q
  · rcases hj with ⟨a,ha⟩
    cases ha
  · rw [typedSourceEquivMatched_root]
    refine (R.fixedB_root hcell hprime u j).trans ?_
    rw [←typedSourceEquivMatched_root (R.blockReference (l:=l)).left (R.blockReference (l:=l)).right p
      (R.blockReference (l:=l)).natDraw (R.blockReference (l:=l)).slot_values (R.blockReference (l:=l)).root_matching j]
    simp only [referenceSample,Function.comp_apply,Equiv.symm_apply_apply]
    rfl
  · rw [typedSourceEquivMatched_block]
    exact (fixedB_representative (R.frame (l:=l) hcell hprime) _ _).trans
      (R.restored_referenceSample_representative u _).symm

end MatchedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
