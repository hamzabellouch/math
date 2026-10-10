import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCanonicalGuardsWeight
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedWindowRegularityMasks

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateOneSidedBudget
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

theorem windowGuardList_good (e : Expr ι) (lo hi : ℝ) (strictUpper : Bool) (a : ι → ℤ)
    (he : HistoryReconstruction.Good a e) :
    ∀q ∈ windowGuardList e lo hi strictUpper,HistoryReconstruction.Good a q.expression := by
  intro q hq
  simp only [windowGuardList,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl <;> exact he

theorem sourceRangeLeafGuards_good (k : ℕ) (J : ℤ) (X Δ W : ℝ)
    (e : Expressions (ι:=ι) k 0) (a : ι → ℤ)
    (he : ∀i,HistoryReconstruction.Good a (e i)) :
    ∀q ∈ sourceRangeLeafGuards k J X Δ W e,HistoryReconstruction.Good a q.expression := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact windowGuardList_good _ _ _ _ a (he _) q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact windowGuardList_good _ _ _ _ a (he _) q hq
  · exact windowGuardList_good _ _ _ _ a (finiteProductExpression_good e a he) q hq

theorem canonicalSourceLeafGuardData_good (k : ℕ) (J : ℤ) (X Δ W : ℝ)
    (j : ℕ) (s : ℤ) (a : State k j) :
    ∀q ∈ canonicalSourceLeafGuardData k J X Δ W j s,
      HistoryReconstruction.Good a q.expression := by
  cases j with
  | zero => exact sourceRangeLeafGuards_good k J X Δ W _ a (fun _ => ⟨trivial,trivial⟩)
  | succ j => intro q hq; exact False.elim (List.not_mem_nil hq)

theorem pivotCellGuards_good (k : ℕ) (V : ℕ → ℤ) (T : ℕ → ℝ) (W : ℝ)
    (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) (a : ι → ℤ)
    (he : ∀i,HistoryReconstruction.Good a (e i))
    (hf : frequencyArithmetic k V j s (evalExpressions a e) t) :
    ∀q ∈ pivotCellGuards k T W j s e t,HistoryReconstruction.Good a q.expression := by
  induction j generalizing s with
  | zero => intro q hq; exact False.elim (List.not_mem_nil hq)
  | succ j ih =>
    let P := pivotExpression k j e s t.1.1 t.1.2
    have hp : HistoryReconstruction.Good a P :=
      pivotExpression_good_of_nodeArithmetic k j e _ _ _ _ a he hf.2.1
    have hfl : frequencyArithmetic k V j t.1.1
        (evalExpressions a (childExpressions k j true e P)) t.2.1 := by
      rw [childExpressions_eval,pivotExpression_eval]
      exact hf.2.2.2.1
    have hfr : frequencyArithmetic k V j t.1.2
        (evalExpressions a (childExpressions k j false e P)) t.2.2 := by
      rw [childExpressions_eval,pivotExpression_eval]
      exact hf.2.2.2.2
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact windowGuardList_good P _ _ _ a hp q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ih _ _ _ (childExpressions_preserves k j true e P _ he hp) hfl q hq
    · exact ih _ _ _ (childExpressions_preserves k j false e P _ he hp) hfr q hq

theorem canonicalSourceGuardList_good (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (X Δ W : ℝ) (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (a : ι → ℤ)
    (he : ∀i,HistoryReconstruction.Good a (e i))
    (hf : frequencyArithmetic k V j s (evalExpressions a e) t) :
    ∀q ∈ canonicalSourceGuardList k B V T J X Δ W j s e t,
      HistoryReconstruction.Good a q.expression := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · rcases List.mem_append.mp hq with hq | hq
    · exact historyGuards_good k B V (fun _ _ => [])
        (fun _ _ _ _ h => False.elim (List.not_mem_nil h)) j s e t a he hf q hq
    · exact pivotCellGuards_good k V T W j s e t a he hf q hq
  · exact maskGuards_good k V (canonicalSourceLeafGuardData k J X Δ W)
      (canonicalSourceLeafGuardData_good k J X Δ W) j s e t a he hf q hq

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
