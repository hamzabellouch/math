import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCoordinatesSmall
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
local instance actualKernelStageCoordinatesProductInternalDecidable (seed : List SourceSlot) (l : ℕ) :
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

theorem probabilityProduct_eq_restored_referenceSample (mixed : Bool)
    (u : SelectedBulkSample C l) :
    probabilityProduct (R.frame (l:=l) hcell hprime) mixed
      (fibreAssignment C (outerNonbulk C l p o) u)=
    ∏r : Representative (R.blockReference (l:=l)).left.history (R.blockReference (l:=l)).right.history,
      actualProbability mixed (R.blockReference (l:=l)).left.history (R.blockReference (l:=l)).right.history
        (R.blockReference (l:=l)).left.supported (R.blockReference (l:=l)).right.supported r
        ((referenceSample (C:=C) (l:=l) (R.blockReference (l:=l)) (restoreOriginalDraw C l p o u)
          (representativeMap (R.blockReference (l:=l)).left.history (R.blockReference (l:=l)).right.history r)).toNat)
        (referenceSample (C:=C) (l:=l) (R.blockReference (l:=l)) (restoreOriginalDraw C l p o u)) := by
  unfold probabilityProduct
  apply Finset.prod_congr rfl
  intro r _
  rw [R.restored_referenceSample_representative u r,Int.toNat_natCast]
  exact actualProbability_congr_small mixed _ _ _ _ r _ _ _
    (R.fixedB_eq_restored_referenceSample_small hcell hprime u)

theorem restored_sampledJacobian_eq (u : SelectedBulkSample C l) :
    sampledJacobian (C:=C) (l:=l) (R.blockReference (l:=l))
      (referenceSample (C:=C) (l:=l) (R.blockReference (l:=l)) (restoreOriginalDraw C l p o u))=
        ∏q : Block p,((outerBlocks C l p o q).val:ℝ) := by
  unfold sampledJacobian
  simp only [R.restored_referenceSample_representative,Int.toNat_natCast]
  exact representative_product_eq_blocks _ (R.blockReference (l:=l)).left.history
    (R.blockReference (l:=l)).right.history (R.blockReference (l:=l)).left.labels (R.blockReference (l:=l)).right.labels p
    (R.blockReference (l:=l)).natDraw (R.blockReference (l:=l)).slot_values (fun n:ℕ=>(n:ℝ))

end MatchedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
