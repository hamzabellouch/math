import OAI.NumberTheory.Ostmann.Characters.HistoryReconstruction
import OAI.NumberTheory.Ostmann.Characters.SymbolicHistory

namespace OAI

namespace Ostmann.Characters.HistoryReconstruction
open SymbolicHistory
variable {ι:Type*}

def expressionProduct : List (Expr ι) → Expr ι
  | [] => .fixed 1
  | e::es => .mul e (expressionProduct es)

theorem expressionProduct_eval (es:List (Expr ι)) (a:ι→ℤ) :
    (expressionProduct es).integerEval a=(es.map (Expr.integerEval a)).prod := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [expressionProduct,Expr.integerEval,List.map_cons,List.prod_cons,ih]

def pivotExpression (m:ℕ) (x:List (Expr ι)) (s v w:ℤ) : Expr ι :=
  .divide (.sub (.mul (.fixed v) (expressionProduct ((x.drop m).take m)))
    (.mul (.fixed w) (expressionProduct (x.take m)))) s

theorem pivotExpression_eval (m:ℕ) (x:List (Expr ι)) (s v w:ℤ) (a:ι→ℤ) :
    (pivotExpression m x s v w).integerEval a=
      pivot m (x.map (Expr.integerEval a)) s v w := by
  simp only [pivotExpression,Expr.integerEval,expressionProduct_eval,pivot,
    rightProduct,leftProduct,List.map_take,List.map_drop]

def childExpressions (plan:Plan) (k:ℕ) (right:Bool) (x:List (Expr ι)) (P:Expr ι) :
    List (Expr ι) :=
  let m := plan.copiedSize k
  let h := if right then (x.drop m).take m else x.take m
  let y := x.drop (2*m)
  let old := P::(h++y)
  (plan.previousOrder k).map (fun i=>old[i]?.getD (.fixed 0))

theorem childExpressions_eval (plan:Plan) (k:ℕ) (right:Bool)
    (x:List (Expr ι)) (P:Expr ι) (a:ι→ℤ) :
    (childExpressions plan k right x P).map (Expr.integerEval a)=
      childState plan k right (x.map (Expr.integerEval a)) (P.integerEval a) := by
  have hg (es:List (Expr ι)) (i:ℕ) :
      (es[i]?.getD (.fixed 0)).integerEval a=
        (es.map (Expr.integerEval a))[i]?.getD 0 := by
    rw [List.getElem?_map]
    cases es[i]? <;> rfl
  cases right <;>
    simp only [childExpressions,childState,Bool.false_eq_true,ite_false,ite_true,
      List.map_map,Function.comp_def,← List.map_take,← List.map_drop,← List.map_append,
      ← List.map_cons] <;>
    exact List.map_congr_left (fun i _=>hg _ i)

def pivots (plan:Plan) : (k:ℕ) → ℤ → List ℤ → Tree k → List ℤ
  | 0,_,_,_ => []
  | k+1,s,x,t =>
      let P := pivot (plan.copiedSize k) x s t.1.1 t.1.2
      P :: (pivots plan k t.1.1 (childState plan k false x P) t.2.1 ++
        pivots plan k t.1.2 (childState plan k true x P) t.2.2)

def leafStates (plan:Plan) : (k:ℕ) → ℤ → List ℤ → Tree k → List (List ℤ)
  | 0,_,x,_ => [x]
  | k+1,s,x,t =>
      let P := pivot (plan.copiedSize k) x s t.1.1 t.1.2
      leafStates plan k t.1.1 (childState plan k false x P) t.2.1 ++
        leafStates plan k t.1.2 (childState plan k true x P) t.2.2

def pivotExpressions (plan:Plan) : (k:ℕ) → ℤ → List (Expr ι) → Tree k → List (Expr ι)
  | 0,_,_,_ => []
  | k+1,s,x,t =>
      let P := pivotExpression (plan.copiedSize k) x s t.1.1 t.1.2
      P :: (pivotExpressions plan k t.1.1 (childExpressions plan k false x P) t.2.1 ++
        pivotExpressions plan k t.1.2 (childExpressions plan k true x P) t.2.2)

def leafExpressions (plan:Plan) : (k:ℕ) → ℤ → List (Expr ι) → Tree k → List (List (Expr ι))
  | 0,_,x,_ => [x]
  | k+1,s,x,t =>
      let P := pivotExpression (plan.copiedSize k) x s t.1.1 t.1.2
      leafExpressions plan k t.1.1 (childExpressions plan k false x P) t.2.1 ++
        leafExpressions plan k t.1.2 (childExpressions plan k true x P) t.2.2

theorem pivotExpressions_eval (plan:Plan) (k:ℕ) (s:ℤ) (x:List (Expr ι)) (t:Tree k) (a:ι→ℤ) :
    (pivotExpressions plan k s x t).map (Expr.integerEval a)=
      pivots plan k s (x.map (Expr.integerEval a)) t := by
  induction k generalizing s x with
  | zero => rfl
  | succ k ih =>
    simp only [pivotExpressions,pivots,List.map_cons,List.map_append,ih,
      childExpressions_eval,pivotExpression_eval]

theorem leafExpressions_eval (plan:Plan) (k:ℕ) (s:ℤ) (x:List (Expr ι)) (t:Tree k) (a:ι→ℤ) :
    (leafExpressions plan k s x t).map (List.map (Expr.integerEval a))=
      leafStates plan k s (x.map (Expr.integerEval a)) t := by
  induction k generalizing s x with
  | zero => rfl
  | succ k ih =>
    simp only [leafExpressions,leafStates,List.map_append,ih,
      childExpressions_eval,pivotExpression_eval]

theorem leafStates_length (plan:Plan) (k:ℕ) (s:ℤ) (x:List ℤ) (t:Tree k) :
    (leafStates plan k s x t).length=2^k := by
  induction k generalizing s x with
  | zero => rfl
  | succ k ih => simp only [leafStates,List.length_append,ih,pow_succ]; omega

end Ostmann.Characters.HistoryReconstruction

end OAI
