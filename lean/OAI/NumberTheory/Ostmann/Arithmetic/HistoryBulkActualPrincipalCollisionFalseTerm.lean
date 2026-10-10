import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalDensity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionFalseDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionIntegral
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionNormalForm

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation HistoryBulkFibreOriginalReference
open HistoryBulkPrincipalCollisionError HistoryBulkFibreIntegralReplacementFrame
open HistoryBulkActualPrincipalCollision HistoryBulkActualGoodPrincipal HistoryPairKernelReplacement
open HistoryBulkActualPrincipalValueFrameMatched
attribute [local instance] Classical.propDecidable
attribute [local instance] actualCollisionIntegralInternalDecidable
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

theorem collisionReference_weighted_cmean_eq_normal (corrected mixed : Bool)
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    referenceKernel (l:=l) (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
      Internal (Template.initial (2*(bulkSize k L/2)) k) l) C
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
      outside (outerNonbulk C l p o) (R.collisionReference hcell hlen hp hV) b mixed *
      (selectedBulkPrior C l).cmean (fun u=> (density (R.frame hcell hp) mixed : ℂ) *
        (R.collisionReference hcell hlen hp hV).value corrected mixed u) =
    rootDensity (R.frame hcell hp) mixed *
      ((∏q : Block p,HistoryPairKernelReplacement.symbolicKernel (l:=l) mixed
        (R.frame hcell hp).left (R.frame hcell hp).right
        (R.frame hcell hp).left_supported (R.frame hcell hp).right_supported
        (R.representative hcell hp q) (b q).val : ℝ):ℂ) *
      bulkMean (R.frame hcell hp) corrected mixed (outerNonbulk C l p o) σ hV := by
  rw [FinitePrior.cmean_mul_left,density_cast,
    R.collisionReference_cmean_eq_frame hcell hlen hp hV corrected mixed]
  unfold referenceKernel
  rw [←mul_assoc]
  congr 1
  exact mul_comm _ _
end MatchedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
