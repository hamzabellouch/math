import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCoordinatesProduct
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageRestored
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelProductReplacementMatchedSelectedSupport

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation
open HistoryBulkFibreOriginalReference HistoryPairRepresentatives HistoryPairKernelReplacement
open HistoryBulkReferencePeriodicMeanSource
attribute [local instance] Classical.propDecidable
local instance kernelStageNormalizeInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
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
  (hout : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem restoredKernelTerm_eq_jacobian_mul
    (symbolic corrected mixed : Bool) (u : SelectedBulkSample C l)
    (hm : originalDrawMass (fun _=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p (restoreOriginalDraw C l p o u)≠0) :
    R.restoredKernelTerm hcell hout hprime hV symbolic corrected mixed u =
      (∏q : Block p,((outerBlocks C l p o q).val:ℂ))*
        R.kernelTerm hcell hout hprime hV symbolic corrected mixed u := by
  have hs := HistoryPairKernelProductReplacement.rightRootSupported_selected_permutation
    C R.blockReference σ R.rootAligned (fun _=>C.giant) (restoreOriginalDraw C l p o u) hm
  have hs1 : HistoryPairKernelProductReplacement.rightRootSupportIndicator
      R.blockReference (fun _=>C.giant) (restoreOriginalDraw C l p o u)=1 := by
    exact ite_eq_left hs
  cases symbolic <;> unfold restoredKernelTerm kernelTerm kernelProduct
  all_goals dsimp only
  all_goals rw [hs1,R.restored_sampledJacobian_eq]
  · simp only [Bool.false_eq_true,ite_false,Complex.ofReal_one,one_mul,
      Complex.ofReal_prod,Complex.ofReal_natCast]
    rw [R.probabilityProduct_eq_restored_referenceSample]
    simp only [Complex.ofReal_prod]
    unfold staticPairMask HistorySignedResidueFactorization.guardIndicator
    split_ifs <;> simp only [one_mul,zero_mul,mul_zero] <;> ac_rfl
  · simp only [ite_true,R.restored_referenceSample_representative,Int.toNat_natCast,
      Complex.ofReal_one,one_mul,Complex.ofReal_prod,Complex.ofReal_natCast]
    unfold staticPairMask HistorySignedResidueFactorization.guardIndicator
    split_ifs <;> simp only [one_mul,zero_mul,mul_zero] <;> ac_rfl

end MatchedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
