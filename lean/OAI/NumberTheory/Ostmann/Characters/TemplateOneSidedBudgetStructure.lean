import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetSampled
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationCanonical

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedBudget
open SymbolicHistory Template TemplateOneSidedCancellation
variable {ι κ : Type*}

def recursiveSizeFactor (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | j+1 => (recursiveSizeFactor k j+1)*(expressionStepFactor k j+1)

theorem recursiveSizeFactor_pos (k j : ℕ) : 0 < recursiveSizeFactor k j := by
  cases j <;> simp only [recursiveSizeFactor] <;> positivity

theorem recursiveExpressions_size (k j : ℕ) (b : Bool) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) (M : ℕ)
    (he : ∀i,(e i).syntaxSize ≤ M) :
    (∀q∈pivotExpressions k j s e t,q.syntaxSize ≤ recursiveSizeFactor k j*(M+1)) ∧
    (∀z∈bottomExpressions k j b s e t,∀i,(z.2.2 i).syntaxSize ≤ recursiveSizeFactor k j*(M+1)) := by
  induction j generalizing b s M with
  | zero =>
    constructor
    · simp only [pivotExpressions,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    · intro z hz i
      have hz' : z=(b,s,e) := List.mem_singleton.mp hz
      subst z
      simpa only [recursiveSizeFactor,one_mul] using (he i).trans (Nat.le_succ M)
  | succ j ih =>
    let C := recursiveSizeFactor k j
    let A := expressionStepFactor k j
    let P := pivotExpression k j e s t.1.1 t.1.2
    have hP : P.syntaxSize ≤ A*(M+1) := pivotExpression_syntaxSize k j e s _ _ M he
    have hc (v : Bool) : ∀i,(childExpressions k j v e P i).syntaxSize ≤ A*(M+1) :=
      childExpressions_syntaxSize k j v e s _ _ M he
    have hl := ih b t.1.1 (childExpressions k j true e P) t.2.1 (A*(M+1)) (hc true)
    have hr := ih (!b) t.1.2 (childExpressions k j false e P) t.2.2 (A*(M+1)) (hc false)
    have hscale : C*(A*(M+1)+1) ≤ ((C+1)*(A+1))*(M+1) := by nlinarith
    have hp : A*(M+1) ≤ ((C+1)*(A+1))*(M+1) := by nlinarith
    constructor
    · intro q hq
      change q∈P::(_++_) at hq
      rcases List.mem_cons.mp hq with hq|hq
      · subst q;exact hP.trans hp
      · rcases List.mem_append.mp hq with hq|hq
        · exact (hl.1 q hq).trans hscale
        · exact (hr.1 q hq).trans hscale
    · intro z hz i
      change z∈(_++_) at hz
      rcases List.mem_append.mp hz with hz|hz
      · exact (hl.2 z hz i).trans hscale
      · exact (hr.2 z hz i).trans hscale

def obstructionSizeFactor (k j : ℕ) : ℕ :=
  (Fintype.card (schedule k 0).Slot+1)*(recursiveSizeFactor k j+1)

theorem obstructionExpressions_size (k j : ℕ) (b : Bool) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) (M : ℕ)
    (he : ∀i,(e i).syntaxSize ≤ M) :
    ∀q∈obstructionExpressions k j b s e t,
      q.syntaxSize ≤ obstructionSizeFactor k j*(M+1) := by
  obtain ⟨hp,hb⟩ := recursiveExpressions_size k j b s e t M he
  intro q hq
  rcases List.mem_append.mp hq with hq|hq
  · have hh := hp q hq
    unfold obstructionSizeFactor
    nlinarith
  · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    have hh := finiteProductExpression_syntaxSize z.2.2 (recursiveSizeFactor k j*(M+1)) (hb z hz)
    change (periodExpression k z.2.2).syntaxSize ≤
      (Fintype.card (schedule k 0).Slot+1)*(recursiveSizeFactor k j*(M+1)+1) at hh
    apply hh.trans
    unfold obstructionSizeFactor
    nlinarith

theorem sampled_obstructions_size (k j : ℕ) (width : Role → ℕ) (m : ℕ)
    (hm : ∀r,width r ≤ m) (b : Bool) (s : ℤ) (t : HistoryReconstruction.Tree j) :
    ∀q∈obstructionExpressions k j b s (sampledExpressions k j width) t,
      q.syntaxSize ≤ (3*obstructionSizeFactor k j)*(m+1) ∧
      q.degreeBudget ≤ (3*obstructionSizeFactor k j)*(m+1) := by
  have hs (i : (schedule k j).Slot) :
      (sampledExpressions k j width i).syntaxSize ≤ 2*(m+1) := by
    exact (sampledExpressions_syntaxSize k j width i).trans (by nlinarith [hm ((schedule k j).role i)])
  intro q hq
  have hq' := obstructionExpressions_size k j b s (sampledExpressions k j width) t _ hs q hq
  have hh : q.syntaxSize ≤ (3*obstructionSizeFactor k j)*(m+1) := by nlinarith
  exact ⟨hh,q.degreeBudget_le_syntaxSize.trans hh⟩

theorem substitute_syntaxSize (x : κ → Expr ι) (e : Expr κ) (M : ℕ)
    (hx : ∀i,(x i).syntaxSize ≤ M) :
    (substitute x e).syntaxSize ≤ e.syntaxSize*(M+1) := by
  induction e with
  | atom i => simpa only [substitute,Expr.syntaxSize,one_mul] using (hx i).trans (Nat.le_succ M)
  | fixed c => simp only [substitute,Expr.syntaxSize,one_mul];omega
  | add a b ia ib | sub a b ia ib | mul a b ia ib =>
    simp only [substitute,Expr.syntaxSize]
    nlinarith
  | divide a d ia =>
    simp only [substitute,Expr.syntaxSize]
    nlinarith

end Ostmann.Characters.TemplateOneSidedBudget

end

end OAI
