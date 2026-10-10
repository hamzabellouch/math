import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterEquivBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCoordinatesRoot
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatchedBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelReplacementGiantFree

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
local instance actualKernelStageCoordinatesInternalDecidable (seed : List SourceSlot) (l : ℕ) :
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

theorem fixedB_root (u : SelectedBulkSample C l)
    (j : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length) :
    (R.frame (l:=l) hcell hprime).fixedB (fibreAssignment C (outerNonbulk C l p o) u)
      (rootKey (R.frame (l:=l) hcell hprime).left (R.frame (l:=l) hcell hprime).right
        (rootPosition (leftDraw (R.frame (l:=l) hcell hprime)) j)) =
      ((fibreAssignment C (outerNonbulk C l p o) u j).val : ℤ) := by
  exact HistoryBulkPrincipalBSquareReference.fixedB_root (R.frame (l:=l) hcell hprime)
    (fibreAssignment C (outerNonbulk C l p o) u)
    (fibreAssignment_nonbulk_fixed C (outerNonbulk C l p o) u R.witness.bulk) j

end MatchedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
