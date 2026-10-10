import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterEquivBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageValue
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatchedBasic

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
local instance kernelStageRestoredInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
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

def restoredKernelTerm (symbolic corrected mixed : Bool) (u : SelectedBulkSample C l) : ℂ :=
  let r := R.frame hcell hprime
  let x := fibreAssignment C (outerNonbulk C l p o) u
  let y := restoreOriginalDraw C l p o u
  let z := HistoryBulkPrincipalKernelReplacementMatched.referenceSample R.blockReference y
  (if mixed then Frame.extractedDensity (C:=C) r.leftSource else 1) *
    (if (((r.newLeft x).root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime ∧
      ((r.newRight (permuteAssignment C σ x)).root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime) then
      (HistoryPairKernelProductReplacement.rightRootSupportIndicator R.blockReference (fun _=>C.giant) y:ℂ)*
        (HistoryBulkPrincipalKernelReplacementMatched.sampledJacobian R.blockReference z:ℂ)*
        (R.principalData hcell (bulkSize k L/2) hout hprime hV true).value corrected mixed u *
        ((∏q : Representative R.blockReference.left.history R.blockReference.right.history,
          if symbolic then symbolicKernel mixed R.blockReference.left.history R.blockReference.right.history
            R.blockReference.left.supported R.blockReference.right.supported q
            (z (HistoryPairRepresentativeVariables.representativeMap R.blockReference.left.history R.blockReference.right.history q)).toNat
          else actualProbability mixed R.blockReference.left.history R.blockReference.right.history
            R.blockReference.left.supported R.blockReference.right.supported q
            (z (HistoryPairRepresentativeVariables.representativeMap R.blockReference.left.history R.blockReference.right.history q)).toNat z:ℝ):ℂ)
    else 0)

end MatchedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
