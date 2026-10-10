import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionNormalForm
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageValue

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation HistoryBulkFibreOriginalReference
open HistoryBulkPrincipalCollisionError
open HistoryBulkActualPrincipalCollision HistoryCompensationRepresentativePatterns
open HistoryPairRepresentatives HistoryPairKernelReplacement HistoryPairReferenceSourceTransport
attribute [local instance] Classical.propDecidable actualCollisionInternalDecidable
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

theorem kernelProduct_symbolic_eq_referenceKernel (mixed : Bool) (u : SelectedBulkSample C l) :
    (R.kernelProduct hcell hp true mixed u:ℂ) =
    referenceKernel C
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
      outside (outerNonbulk C l p o) (R.collisionReference hcell hlen hp hV)
      (outerBlocks C l p o) mixed := by
  have hh (q : Block p) :
      prime R.blockReference.left.history R.blockReference.right.history
        (R.representative hcell hp q)=(outerBlocks C l p o q).val := by
    have he := representativeBlockEquiv_prime _ R.blockReference.left.history
      R.blockReference.right.history R.blockReference.left.labels R.blockReference.right.labels p
      R.blockReference.natDraw R.blockReference.slot_values (R.representative hcell hp q)
    change prime R.blockReference.left.history R.blockReference.right.history
      (R.representative hcell hp q)=R.blockReference.natDraw.val
        ((R.representative hcell hp).symm (R.representative hcell hp q)) at he
    rw [Equiv.symm_apply_apply] at he
    exact he.trans (by rfl)
  unfold kernelProduct referenceKernel
  simp only [ite_true]
  apply congrArg (fun z:ℝ=>(z:ℂ))
  exact symbolic_product_eq_blocks R.blockReference.left.history R.blockReference.right.history
    R.blockReference.left.supported R.blockReference.right.supported
    (R.representative hcell hp) (fun q=>(outerBlocks C l p o q).val) hh mixed

end MatchedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
