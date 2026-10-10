import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCoordinates

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
local instance actualKernelStageRepresentativeInternalDecidable (seed : List SourceSlot) (l : ℕ) :
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

theorem restored_referenceSample_representative (u : SelectedBulkSample C l)
    (r : Representative (R.blockReference (l:=l)).left.history (R.blockReference (l:=l)).right.history) :
    referenceSample (C:=C) (l:=l) (R.blockReference (l:=l)) (restoreOriginalDraw C l p o u)
      (representativeMap (R.blockReference (l:=l)).left.history (R.blockReference (l:=l)).right.history r)=
      (prime (R.blockReference (l:=l)).left.history (R.blockReference (l:=l)).right.history r:ℤ) := by
  let e := typedBlockEquiv (R.blockReference (l:=l)).left (R.blockReference (l:=l)).right p
    (R.blockReference (l:=l)).natDraw (R.blockReference (l:=l)).slot_values
  have hk := typedSourceEquivMatched_block (R.blockReference (l:=l)).left (R.blockReference (l:=l)).right p
    (R.blockReference (l:=l)).natDraw (R.blockReference (l:=l)).slot_values (R.blockReference (l:=l)).root_matching (e r)
  rw [Equiv.symm_apply_apply] at hk
  rw [←hk]
  simp only [referenceSample,Function.comp_apply,Equiv.symm_apply_apply]
  have hp := representativeBlockEquiv_prime _ (R.blockReference (l:=l)).left.history
    (R.blockReference (l:=l)).right.history (R.blockReference (l:=l)).left.labels (R.blockReference (l:=l)).right.labels p
    (R.blockReference (l:=l)).natDraw (R.blockReference (l:=l)).slot_values r
  exact congrArg (fun n:ℕ=>(n:ℤ)) hp.symm

end MatchedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
