import OAI.NumberTheory.Ostmann.Characters.HistorySymbolicTrace
import OAI.NumberTheory.Ostmann.Characters.ZeroVariable

namespace OAI

namespace Ostmann.Characters.HistoryReconstruction
open SymbolicHistory
variable {ι:Type*}

def Good (a:ι→ℤ) (e:Expr ι) : Prop := e.Valid ∧ e.IntegralAt a

theorem expressionProduct_good (a:ι→ℤ) (es:List (Expr ι))
    (h:∀e∈es,Good a e) : Good a (expressionProduct es) := by
  induction es with
  | nil => exact ⟨trivial,trivial⟩
  | cons e es ih =>
    have he := h e List.mem_cons_self
    have ht := ih (fun e he=>h e (List.mem_cons_of_mem _ he))
    exact ⟨⟨he.1,ht.1⟩,⟨he.2,ht.2⟩⟩

theorem childExpressions_preserves (R:Expr ι→Prop) (hzero:R (.fixed 0))
    (plan:Plan) (k:ℕ) (right:Bool) (x:List (Expr ι)) (P:Expr ι)
    (hx:∀e∈x,R e) (hP:R P) : ∀e∈childExpressions plan k right x P,R e := by
  let m := plan.copiedSize k
  let h := if right then (x.drop m).take m else x.take m
  have hh : ∀e∈h,R e := by
    intro e he
    cases right with
    | false => exact hx e (List.mem_of_mem_take he)
    | true => exact hx e (List.mem_of_mem_drop (List.mem_of_mem_take he))
  have hold : ∀e∈P::(h++x.drop (2*m)),R e := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hP
    · rcases List.mem_append.mp he with he | he
      · exact hh e he
      · exact hx e (List.mem_of_mem_drop he)
  intro e he
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
  change R (((P::(h++x.drop (2*m)))[i]?).getD (.fixed 0))
  cases hg:(P::(h++x.drop (2*m)))[i]? with
  | none => exact hzero
  | some q => exact hold q (List.mem_of_getElem? hg)

theorem pivotExpression_good (a:ι→ℤ) (m:ℕ) (x:List (Expr ι)) (s v w B V:ℤ)
    (hx:∀e∈x,Good a e) (h:NodeValid m (x.map (Expr.integerEval a)) s v w B V) :
    Good a (pivotExpression m x s v w) := by
  have hL := expressionProduct_good a (x.take m) (fun e he=>hx e (List.mem_of_mem_take he))
  have hR := expressionProduct_good a ((x.drop m).take m)
    (fun e he=>hx e (List.mem_of_mem_drop (List.mem_of_mem_take he)))
  refine ⟨⟨⟨⟨trivial,hR.1⟩,⟨trivial,hL.1⟩⟩,h.root_ne_zero⟩,
    ⟨⟨⟨trivial,hR.2⟩,⟨trivial,hL.2⟩⟩,?_⟩⟩
  simpa only [Expr.integerEval,expressionProduct_eval,leftProduct,rightProduct,
    List.map_drop,List.map_take] using h.integral

theorem pivotExpressions_good (plan:Plan) (B V:ℕ→List ℤ→ℤ) (k:ℕ) (s:ℤ)
    (x:List (Expr ι)) (t:Tree k) (a:ι→ℤ) (hx:∀e∈x,Good a e)
    (h:Valid plan B V k s (x.map (Expr.integerEval a)) t) :
    ∀e∈pivotExpressions plan k s x t,Good a e := by
  induction k generalizing s x with
  | zero => simp only [pivotExpressions,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | succ k ih =>
    let P := pivotExpression (plan.copiedSize k) x s t.1.1 t.1.2
    have hP : Good a P := pivotExpression_good a _ x _ _ _ _ _ hx h.1
    have hcl := childExpressions_preserves (Good a) ⟨trivial,trivial⟩ plan k false x P hx hP
    have hcr := childExpressions_preserves (Good a) ⟨trivial,trivial⟩ plan k true x P hx hP
    have hvl : Valid plan B V k t.1.1
        ((childExpressions plan k false x P).map (Expr.integerEval a)) t.2.1 := by
      rw [childExpressions_eval]
      rw [show P.integerEval a=pivot (plan.copiedSize k) (x.map (Expr.integerEval a)) s t.1.1 t.1.2
        from pivotExpression_eval _ _ _ _ _ _]
      exact h.2.1
    have hvr : Valid plan B V k t.1.2
        ((childExpressions plan k true x P).map (Expr.integerEval a)) t.2.2 := by
      rw [childExpressions_eval]
      rw [show P.integerEval a=pivot (plan.copiedSize k) (x.map (Expr.integerEval a)) s t.1.1 t.1.2
        from pivotExpression_eval _ _ _ _ _ _]
      exact h.2.2
    intro e he
    rcases List.mem_cons.mp he with he | he
    · subst e; exact hP
    · rcases List.mem_append.mp he with he | he
      · exact ih _ _ t.2.1 hcl hvl e he
      · exact ih _ _ t.2.2 hcr hvr e he

theorem pivot_cleared (plan:Plan) (B V:ℕ→List ℤ→ℤ) (k:ℕ) (s:ℤ)
    (x:List (Expr ι)) (t:Tree k) (a:ι→ℤ) (hx:∀e∈x,Good a e)
    (h:Valid plan B V k s (x.map (Expr.integerEval a)) t)
    (e:Expr ι) (he:e∈pivotExpressions plan k s x t) :
    e.denominator≠0 ∧ e.denominator*e.integerEval a=MvPolynomial.eval a e.numerator := by
  have hg := pivotExpressions_good plan B V k s x t a hx h e he
  exact ⟨e.denominator_ne_zero hg.1,e.integerEval_cleared a hg.2⟩

end Ostmann.Characters.HistoryReconstruction

end OAI
