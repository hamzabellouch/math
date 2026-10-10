import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalCorrectedReferenceBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualGoodPrincipal HistoryBulkIndependentFibreReference
attribute [local instance] Classical.propDecidable
private theorem option_guard_eq {α : Type} (P : Prop) [Decidable P]
    (hp : α→P) (o : Option α) (f : α→ℂ) :
    (if P then o.elim 0 f else 0)=o.elim 0 f := by
  cases o with
  | none => simp only [Option.elim_none,ite_self]
  | some x => rw [ite_eq_left (hp x)]

variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
  (outside : List ℕ) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))

theorem selectedCorrectedOuter_elim_typed
    (F : CorrectedSelectedOuter (l:=l) C p o outside e i → ℂ) :
    (if Function.Injective (fun q=>(blockType p q,outerBlocks C l p o q)) then
      (selectCorrectedOuterReference (l:=l) C p o outside e i).elim 0 F else 0)=
      (selectCorrectedOuterReference (l:=l) C p o outside e i).elim 0 F :=
  option_guard_eq (α:=CorrectedSelectedOuter (l:=l) C p o outside e i)
    (Function.Injective (fun q=>(blockType p q,outerBlocks C l p o q)))
    (fun R=>R.data.typed) (selectCorrectedOuterReference (l:=l) C p o outside e i) F

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
