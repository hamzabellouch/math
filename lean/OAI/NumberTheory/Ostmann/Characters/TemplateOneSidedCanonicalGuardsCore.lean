import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationCore
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCanonicalGuardsPivot

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

theorem coreSupport_pivotCells_iff (k : ℕ)
    (B V : (j : ℕ) → State k (j+1) → ℤ) (T : ℕ → ℝ) (W : ℝ)
    (j : ℕ) (s : ℤ) (x : State k j) (t : HistoryReconstruction.Tree j) :
    TransferCoreSupport k B V (canonicalHistoryExtra k (fun l => pivotWindow (T l) W)) j s x t ↔
      TransferCoreSupport k B V (fun _ _ _ _ => True) j s x t ∧
        pivotCellsOnHistory k T W j s x t := by
  induction j generalizing s with
  | zero => simp [TransferCoreSupport,pivotCellsOnHistory,canonicalHistoryExtra]
  | succ j ih =>
    simp only [TransferCoreSupport,pivotCellsOnHistory,ih]
    tauto

def canonicalPivotCoreGuards (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ) (W : ℝ)
    (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) : List (Guard ι) :=
  historyGuards k B V (fun _ _ => []) j s e t ++ pivotCellGuards k T W j s e t

theorem canonicalPivotCoreSupport_iff (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ) (W : ℝ)
    (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) (a : ι → ℤ) :
    TransferCoreSupport k (fun l _ => B l) (fun l _ => V l)
      (canonicalHistoryExtra k (fun l => pivotWindow (T l) W)) j s (evalExpressions a e) t ↔
      frequencyArithmetic k V j s (evalExpressions a e) t ∧
        guardsHold (canonicalPivotCoreGuards k B V T W j s e t) a := by
  have hbase := canonicalCoreSupport_iff k B V (fun _ _ => []) j s e t a
  have hmask : (fun l s x (_t : HistoryReconstruction.Tree l) =>
      canonicalMask k (fun _ _ => []) l s x) = (fun _ _ _ _ => True) := by
    funext l s x t
    apply propext
    simp [canonicalMask,guardsHold]
  rw [hmask] at hbase
  rw [coreSupport_pivotCells_iff,hbase,←pivotCellGuards_holds k T W j s e t a]
  simp only [canonicalPivotCoreGuards,guardsHold_append]
  tauto

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
