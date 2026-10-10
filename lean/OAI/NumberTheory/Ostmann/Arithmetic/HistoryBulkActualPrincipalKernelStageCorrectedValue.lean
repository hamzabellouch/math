import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamilyData
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexCorrectedDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation
open HistoryBulkFibreOriginalReference HistoryBulkIndependentFibreReference
open HistoryPairRepresentatives HistoryPairKernelReplacement HistoryBulkReferencePeriodicMeanSource
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualCorrectedPrincipalBlockFamily
attribute [local instance] Classical.propDecidable
local instance correctedKernelStageValueInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ} {e : RemainingPermutation (k:=k) (L:=L) (l:=l)}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}
namespace CorrectedSelectedOuter
variable (R : CorrectedSelectedOuter C p o outside e i)
  (he : PreservesRemainingBands _ e)
  (hout : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

def kernelStatic (u : SelectedBulkSample C l) : Prop :=
  let r := R.frame he hprime
  let x := fibreAssignment C (outerNonbulk C l p o) u
  ((r.newLeft x).root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime ∧
    ((r.newRight (R.squareRightSource he u)).root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime

def kernelProduct (symbolic : Bool) (u : SelectedBulkSample C l) : ℝ :=
  if symbolic then
    ∏r : Representative (R.blockReference he).left.history (R.blockReference he).right.history,
      symbolicKernel true (R.blockReference he).left.history (R.blockReference he).right.history
        (R.blockReference he).left.supported (R.blockReference he).right.supported r
        (prime (R.blockReference he).left.history (R.blockReference he).right.history r)
  else HistoryBulkPrincipalBSquareReference.probabilityProduct (R.frame he hprime) true
    (fibreAssignment C (outerNonbulk C l p o) u)

def kernelTerm (symbolic : Bool) (u : SelectedBulkSample C l) : ℂ :=
  let r := R.frame he hprime
  let x := fibreAssignment C (outerNonbulk C l p o) u
  staticPairMask (r.newLeft x) (r.newRight (R.squareRightSource he u)) outside *
    (Frame.extractedDensity (C:=C) r.leftSource *
      ((principalData R he (bulkSize k L/2) hout hprime hV).value true true u *
        (R.kernelProduct he hprime symbolic u:ℂ)))

end CorrectedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
