import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCanonicalGuardsGood

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateOneSidedBudget
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

theorem windowGuardList_expression (e : Expr ι) (lo hi : ℝ) (strictUpper : Bool)
    (q : Guard ι) (hq : q ∈ windowGuardList e lo hi strictUpper) : q.expression=e := by
  simp only [windowGuardList,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl <;> rfl

theorem pivotCellGuards_expression_mem (k : ℕ) (T : ℕ → ℝ) (W : ℝ)
    (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
    (q : Guard ι) (hq : q ∈ pivotCellGuards k T W j s e t) :
    q.expression ∈ pivotExpressions k j s e t := by
  induction j generalizing s with
  | zero => exact False.elim (List.not_mem_nil hq)
  | succ j ih =>
    rcases List.mem_append.mp hq with hq | hq
    · rw [windowGuardList_expression _ _ _ _ q hq]
      exact List.mem_cons_self
    rcases List.mem_append.mp hq with hq | hq
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ih _ _ _ hq))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih _ _ _ hq))

theorem pivotCellGuards_length (k : ℕ) (T : ℕ → ℝ) (W : ℝ)
    (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) :
    (pivotCellGuards k T W j s e t).length + 2 = 2^(j+1) := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    have hl := ih t.1.1 (childExpressions k j true e (pivotExpression k j e s t.1.1 t.1.2)) t.2.1
    have hr := ih t.1.2 (childExpressions k j false e (pivotExpression k j e s t.1.1 t.1.2)) t.2.2
    simp only [pivotCellGuards,List.length_append,windowGuardList,List.length_cons,List.length_nil]
    rw [pow_succ]
    omega

theorem sourceLeafMaskGuards_length (k : ℕ) (J : ℤ) (X Δ W : ℝ)
    (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) :
    (maskGuards k (canonicalSourceLeafGuardData k J X Δ W) j s e t).length = 6*2^j := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    simp only [maskGuards,canonicalSourceLeafGuardData,List.map_nil,List.nil_append,List.length_append,ih,pow_succ]
    ring

theorem canonicalSourceGuardList_length_le (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (X Δ W : ℝ) (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) :
    (canonicalSourceGuardList k B V T J X Δ W j s e t).length ≤ guardCountFactor k j+8*2^j := by
  have hh := historyGuards_length k j B V (fun _ _ => []) 0 (by simp) s e t
  have hp := pivotCellGuards_length k T W j s e t
  have hm := sourceLeafMaskGuards_length k J X Δ W j s e t
  simp only [Nat.zero_add,Nat.mul_one] at hh
  simp only [canonicalSourceGuardList,canonicalPivotCoreGuards,List.length_append,hm]
  rw [pow_succ] at hp
  omega

theorem pivotCellGuards_size (k : ℕ) (T : ℕ → ℝ) (W : ℝ)
    (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
    (M : ℕ) (he : ∀i,(e i).syntaxSize ≤ M) :
    ∀q ∈ pivotCellGuards k T W j s e t,q.expression.syntaxSize ≤ recursiveSizeFactor k j*(M+1) := by
  intro q hq
  exact (recursiveExpressions_size k j false s e t M he).1 q.expression
    (pivotCellGuards_expression_mem k T W j s e t q hq)

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
