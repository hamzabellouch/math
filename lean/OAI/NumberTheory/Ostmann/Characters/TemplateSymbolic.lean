import OAI.NumberTheory.Ostmann.Characters.HistorySymbolicSupport
import OAI.NumberTheory.Ostmann.Characters.TemplateHistory

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open SymbolicHistory
attribute [local instance] Classical.propDecidable
variable {ι:Type*}

def finiteProductExpression {α:Type*} [Fintype α] (e:α→Expr ι) : Expr ι :=
  HistoryReconstruction.expressionProduct
    (List.ofFn (fun i:Fin (Fintype.card α)=>e ((Fintype.equivFin α).symm i)))

theorem finiteProductExpression_eval {α:Type*} [Fintype α] (e:α→Expr ι) (a:ι→ℤ) :
    (finiteProductExpression e).integerEval a=∏i,(e i).integerEval a := by
  rw [finiteProductExpression,HistoryReconstruction.expressionProduct_eval,List.map_ofFn,List.prod_ofFn]
  exact (Fintype.equivFin α).symm.prod_comp (fun i=>(e i).integerEval a)

theorem finiteProductExpression_good {α:Type*} [Fintype α] (e:α→Expr ι) (a:ι→ℤ)
    (h:∀i,HistoryReconstruction.Good a (e i)) :
    HistoryReconstruction.Good a (finiteProductExpression e) := by
  apply HistoryReconstruction.expressionProduct_good
  intro q hq
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hq
  rw [← hi]
  exact h _

abbrev Expressions (k j:ℕ) := (schedule k j).Slot → Expr ι

def evalExpressions (a:ι→ℤ) {k j:ℕ} (e:Expressions (ι:=ι) k j) : State k j :=
  fun i=>(e i).integerEval a

def copiedExpression (k j:ℕ) (b:Bool) (e:Expressions (ι:=ι) k (j+1)) : Expr ι :=
  finiteProductExpression (fun i:{i:(schedule k j).Slot // (schedule k j).IsCopied j i}=>
    e (.inl (i,b)))

def pivotExpression (k j:ℕ) (e:Expressions (ι:=ι) k (j+1)) (s v w:ℤ) : Expr ι :=
  .divide (.sub (.mul (.fixed v) (copiedExpression k j false e))
    (.mul (.fixed w) (copiedExpression k j true e))) s

def childExpressions (k j:ℕ) (b:Bool) (e:Expressions (ι:=ι) k (j+1)) (P:Expr ι) :
    Expressions (ι:=ι) k j := fun i=>
  if hp:(schedule k j).IsPivot j i then P
  else if hc:(schedule k j).IsCopied j i then e (.inl (⟨i,hc⟩,b))
  else e (.inr ⟨i,⟨hp,hc⟩⟩)

theorem copiedExpression_eval (k j:ℕ) (b:Bool) (e:Expressions (ι:=ι) k (j+1)) (a:ι→ℤ) :
    (copiedExpression k j b e).integerEval a=copiedProduct k j b (evalExpressions a e) := by
  exact finiteProductExpression_eval _ _

theorem pivotExpression_eval (k j:ℕ) (e:Expressions (ι:=ι) k (j+1)) (s v w:ℤ) (a:ι→ℤ) :
    (pivotExpression k j e s v w).integerEval a=
      reconstructedPivot k j (evalExpressions a e) s v w := by
  simp only [pivotExpression,Expr.integerEval,copiedExpression_eval,reconstructedPivot]

theorem childExpressions_eval (k j:ℕ) (b:Bool) (e:Expressions (ι:=ι) k (j+1))
    (P:Expr ι) (a:ι→ℤ) :
    evalExpressions a (childExpressions k j b e P)=
      childState k j b (evalExpressions a e) (P.integerEval a) := by
  funext i
  unfold evalExpressions childExpressions childState
  split_ifs <;> rfl

theorem childExpressions_preserves (k j:ℕ) (b:Bool) (e:Expressions (ι:=ι) k (j+1))
    (P:Expr ι) (R:Expr ι→Prop) (he:∀i,R (e i)) (hP:R P) :
    ∀i,R (childExpressions k j b e P i) := by
  intro i
  unfold childExpressions
  split_ifs
  · exact hP
  · exact he _
  · exact he _

theorem pivotExpression_good (k j:ℕ) (e:Expressions (ι:=ι) k (j+1))
    (s v w B V:ℤ) (a:ι→ℤ) (he:∀i,HistoryReconstruction.Good a (e i))
    (h:NodeSupported k j (evalExpressions a e) s v w B V) :
    HistoryReconstruction.Good a (pivotExpression k j e s v w) := by
  have hL := finiteProductExpression_good
    (fun i:{i:(schedule k j).Slot // (schedule k j).IsCopied j i}=>e (.inl (i,true))) a
    (fun i=>he _)
  have hR := finiteProductExpression_good
    (fun i:{i:(schedule k j).Slot // (schedule k j).IsCopied j i}=>e (.inl (i,false))) a
    (fun i=>he _)
  refine ⟨⟨⟨⟨trivial,hR.1⟩,⟨trivial,hL.1⟩⟩,h.root_ne_zero⟩,
    ⟨⟨⟨trivial,hR.2⟩,⟨trivial,hL.2⟩⟩,?_⟩⟩
  simpa only [Expr.integerEval,copiedExpression_eval] using h.integral

def pivots (k:ℕ) : (j:ℕ)→ℤ→State k j→HistoryReconstruction.Tree j→List ℤ
  | 0,_,_,_ => []
  | j+1,s,x,t =>
      let P := reconstructedPivot k j x s t.1.1 t.1.2
      P::(pivots k j t.1.1 (childState k j true x P) t.2.1 ++
        pivots k j t.1.2 (childState k j false x P) t.2.2)

def pivotExpressions (k:ℕ) : (j:ℕ)→ℤ→Expressions (ι:=ι) k j→
    HistoryReconstruction.Tree j→List (Expr ι)
  | 0,_,_,_ => []
  | j+1,s,e,t =>
      let P := pivotExpression k j e s t.1.1 t.1.2
      P::(pivotExpressions k j t.1.1 (childExpressions k j true e P) t.2.1 ++
        pivotExpressions k j t.1.2 (childExpressions k j false e P) t.2.2)

theorem pivotExpressions_eval (k j:ℕ) (s:ℤ) (e:Expressions (ι:=ι) k j)
    (t:HistoryReconstruction.Tree j) (a:ι→ℤ) :
    (pivotExpressions k j s e t).map (Expr.integerEval a)=pivots k j s (evalExpressions a e) t := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih => simp only [pivotExpressions,pivots,List.map_cons,List.map_append,ih,
      childExpressions_eval,pivotExpression_eval]

theorem pivotExpressions_good (k:ℕ) (B V:(j:ℕ)→State k (j+1)→ℤ) (j:ℕ)
    (s:ℤ) (e:Expressions (ι:=ι) k j) (t:HistoryReconstruction.Tree j) (a:ι→ℤ)
    (he:∀i,HistoryReconstruction.Good a (e i))
    (h:Supported k B V j s (evalExpressions a e) t) :
    ∀q∈pivotExpressions k j s e t,HistoryReconstruction.Good a q := by
  induction j generalizing s with
  | zero => simp only [pivotExpressions,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | succ j ih =>
    let P := pivotExpression k j e s t.1.1 t.1.2
    have hP : HistoryReconstruction.Good a P := pivotExpression_good k j e _ _ _ _ _ a he h.1
    have hleft : Supported k B V j t.1.1
        (evalExpressions a (childExpressions k j true e P)) t.2.1 := by
      rw [childExpressions_eval]
      rw [show P.integerEval a=reconstructedPivot k j (evalExpressions a e) s t.1.1 t.1.2
        from pivotExpression_eval _ _ _ _ _ _ _]
      exact h.2.1
    have hright : Supported k B V j t.1.2
        (evalExpressions a (childExpressions k j false e P)) t.2.2 := by
      rw [childExpressions_eval]
      rw [show P.integerEval a=reconstructedPivot k j (evalExpressions a e) s t.1.1 t.1.2
        from pivotExpression_eval _ _ _ _ _ _ _]
      exact h.2.2
    intro q hq
    rcases List.mem_cons.mp hq with hq|hq
    · subst q; exact hP
    · rcases List.mem_append.mp hq with hq|hq
      · exact ih _ _ t.2.1 (childExpressions_preserves k j true e P _ he hP) hleft q hq
      · exact ih _ _ t.2.2 (childExpressions_preserves k j false e P _ he hP) hright q hq

theorem pivot_cleared (k:ℕ) (B V:(j:ℕ)→State k (j+1)→ℤ) (j:ℕ)
    (s:ℤ) (e:Expressions (ι:=ι) k j) (t:HistoryReconstruction.Tree j) (a:ι→ℤ)
    (he:∀i,HistoryReconstruction.Good a (e i))
    (h:Supported k B V j s (evalExpressions a e) t)
    (q:Expr ι) (hq:q∈pivotExpressions k j s e t) :
    q.denominator≠0 ∧ q.denominator*q.integerEval a=MvPolynomial.eval a q.numerator := by
  have hg := pivotExpressions_good k B V j s e t a he h q hq
  exact ⟨q.denominator_ne_zero hg.1,q.integerEval_cleared a hg.2⟩

end Ostmann.Characters.Template

end

end OAI
