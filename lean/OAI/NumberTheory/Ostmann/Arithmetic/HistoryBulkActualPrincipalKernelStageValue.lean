import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferenceBasic

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
local instance kernelStageValueInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
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

def kernelProduct (symbolic mixed : Bool) (u : SelectedBulkSample C l) : ℝ :=
  if symbolic then
    ∏r : Representative R.blockReference.left.history R.blockReference.right.history,
      symbolicKernel mixed R.blockReference.left.history R.blockReference.right.history
        R.blockReference.left.supported R.blockReference.right.supported r
        (prime R.blockReference.left.history R.blockReference.right.history r)
  else HistoryBulkPrincipalBSquareReference.probabilityProduct (R.frame hcell hprime) mixed
    (fibreAssignment C (outerNonbulk C l p o) u)

def kernelTerm (symbolic corrected mixed : Bool) (u : SelectedBulkSample C l) : ℂ :=
  let r := R.frame hcell hprime
  let x := fibreAssignment C (outerNonbulk C l p o) u
  staticPairMask (r.newLeft x) (r.newRight (permuteAssignment C σ x)) outside *
    ((if mixed then Frame.extractedDensity (C:=C) r.leftSource else 1)*
      ((R.principalData hcell (bulkSize k L/2) hout hprime hV true).value corrected mixed u *
        (R.kernelProduct hcell hprime symbolic mixed u:ℂ)))

end MatchedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
