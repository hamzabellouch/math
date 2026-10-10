import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceCanonical
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsPivotRange
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSubstitution

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

def windowGuardList (e : Expr ι) (lo hi : ℝ) (strictUpper : Bool) : List (Guard ι) :=
  [windowGuards e lo hi strictUpper false,windowGuards e lo hi strictUpper true]

theorem windowGuardList_holds (e : Expr ι) (lo hi : ℝ) (strictUpper : Bool) (a : ι → ℤ) :
    guardsHold (windowGuardList e lo hi strictUpper) a ↔
      lo ≤ (e.integerEval a : ℝ) ∧
        (if strictUpper then (e.integerEval a : ℝ) < hi else (e.integerEval a : ℝ) ≤ hi) := by
  cases strictUpper <;> simp [windowGuardList,guardsHold,windowGuards,Guard.holds]

theorem integer_mem_pivotWindow_iff (T W : ℝ) (z : ℤ) :
    (∃P ∈ pivotWindow T W,z = (P:ℤ)) ↔
      Real.exp (T-W) ≤ (z:ℝ) ∧ (z:ℝ) ≤ Real.exp (T+W) := by
  constructor
  · rintro ⟨P,hP,rfl⟩
    simpa only [Int.cast_natCast] using (mem_pivotWindow T W P).mp hP
  · intro h
    have hzR : 0 < (z:ℝ) := (Real.exp_pos (T-W)).trans_le h.1
    have hz : 0 < z := by exact_mod_cast hzR
    let P := positivePivotOfPos z hz
    have he : (P:ℤ) = z := Int.toNat_of_nonneg hz.le
    have heR : (P:ℝ) = (z:ℝ) := by exact_mod_cast he
    exact ⟨P,(mem_pivotWindow T W P).mpr (by simpa only [heR] using h),he.symm⟩

def pivotCellsOnHistory (k : ℕ) (T : ℕ → ℝ) (W : ℝ) :
    (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop
  | 0,_,_,_ => True
  | j+1,s,x,t =>
      canonicalHistoryExtra k (fun l => pivotWindow (T l) W) (j+1) s x t ∧
      pivotCellsOnHistory k T W j t.1.1
        (childState k j true x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.1 ∧
      pivotCellsOnHistory k T W j t.1.2
        (childState k j false x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.2

def pivotCellGuards (k : ℕ) (T : ℕ → ℝ) (W : ℝ) :
    (j : ℕ) → ℤ → Expressions (ι:=ι) k j → HistoryReconstruction.Tree j → List (Guard ι)
  | 0,_,_,_ => []
  | j+1,s,e,t =>
      let P := pivotExpression k j e s t.1.1 t.1.2
      windowGuardList P (Real.exp (T j-W)) (Real.exp (T j+W)) false ++
      (pivotCellGuards k T W j t.1.1 (childExpressions k j true e P) t.2.1 ++
       pivotCellGuards k T W j t.1.2 (childExpressions k j false e P) t.2.2)

theorem pivotCellGuards_holds (k : ℕ) (T : ℕ → ℝ) (W : ℝ) (j : ℕ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) (a : ι → ℤ) :
    guardsHold (pivotCellGuards k T W j s e t) a ↔
      pivotCellsOnHistory k T W j s (evalExpressions a e) t := by
  induction j generalizing s with
  | zero => simp [pivotCellGuards,pivotCellsOnHistory,guardsHold]
  | succ j ih =>
    simp only [pivotCellGuards,pivotCellsOnHistory,guardsHold_append,windowGuardList_holds,
      Bool.false_eq_true,ite_false,ih,childExpressions_eval,pivotExpression_eval,
      canonicalHistoryExtra,integer_mem_pivotWindow_iff]

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
