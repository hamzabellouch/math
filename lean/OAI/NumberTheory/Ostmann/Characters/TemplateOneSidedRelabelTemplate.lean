import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedLeafProfilesBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedRelabelExpr

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedRelabel
open SymbolicHistory TemplateOneSidedCancellation Template
variable {ι κ ν : Type*}

@[simp] theorem relabel_substitute (π : ι → κ) (x : ν → Expr ι) (e : Expr ν) :
    relabel π (substitute x e) = substitute (fun i=>relabel π (x i)) e := by
  induction e <;> simp_all [relabel,substitute]

@[simp] theorem relabel_expressionProduct (π : ι → κ) (es : List (Expr ι)) :
    relabel π (HistoryReconstruction.expressionProduct es) =
      HistoryReconstruction.expressionProduct (es.map (relabel π)) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change Expr.mul (relabel π e) (relabel π (HistoryReconstruction.expressionProduct es)) =
      Expr.mul (relabel π e) (HistoryReconstruction.expressionProduct (es.map (relabel π)))
    exact congrArg (Expr.mul (relabel π e)) ih

@[simp] theorem relabel_finiteProductExpression (π : ι → κ) {α : Type*} [Fintype α]
    (e : α → Expr ι) :
    relabel π (finiteProductExpression e) = finiteProductExpression (fun i=>relabel π (e i)) := by
  simp only [finiteProductExpression,relabel_expressionProduct,List.map_ofFn,Function.comp_def]

def relabelExpressions (π : ι → κ) {k j : ℕ} (e : Expressions (ι:=ι) k j) :
    Expressions (ι:=κ) k j := fun i=>relabel π (e i)

@[simp] theorem relabelExpressions_eval (π : ι → κ) {k j : ℕ}
    (e : Expressions (ι:=ι) k j) (a : κ → ℤ) :
    evalExpressions a (relabelExpressions π e) = evalExpressions (fun i=>a (π i)) e := by
  funext i
  exact relabel_integerEval π (e i) a

@[simp] theorem copiedExpression_relabel (π : ι → κ) (k j : ℕ) (b : Bool)
    (e : Expressions (ι:=ι) k (j+1)) :
    copiedExpression k j b (relabelExpressions π e) = relabel π (copiedExpression k j b e) := by
  simp only [copiedExpression,relabel_finiteProductExpression,relabelExpressions]

@[simp] theorem pivotExpression_relabel (π : ι → κ) (k j : ℕ)
    (e : Expressions (ι:=ι) k (j+1)) (s v w : ℤ) :
    pivotExpression k j (relabelExpressions π e) s v w = relabel π (pivotExpression k j e s v w) := by
  unfold pivotExpression
  rw [copiedExpression_relabel,copiedExpression_relabel]
  rfl

@[simp] theorem childExpressions_relabel (π : ι → κ) (k j : ℕ) (b : Bool)
    (e : Expressions (ι:=ι) k (j+1)) (P : Expr ι) :
    childExpressions k j b (relabelExpressions π e) (relabel π P) =
      relabelExpressions π (childExpressions k j b e P) := by
  funext i
  dsimp only [childExpressions,relabelExpressions]
  split_ifs <;> rfl

@[simp] theorem pivotExpressions_relabel (π : ι → κ) (k j : ℕ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) :
    pivotExpressions k j s (relabelExpressions π e) t =
      (pivotExpressions k j s e t).map (relabel π) := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih => simp only [pivotExpressions,pivotExpression_relabel,childExpressions_relabel,
      ih,List.map_cons,List.map_append]

def relabelBottom (π : ι → κ) {k : ℕ} (z : BottomExpression (ι:=ι) k) :
    BottomExpression (ι:=κ) k := (z.1,z.2.1,relabelExpressions π z.2.2)

@[simp] theorem bottomExpressions_relabel (π : ι → κ) (k j : ℕ) (b : Bool) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) :
    bottomExpressions k j b s (relabelExpressions π e) t =
      (bottomExpressions k j b s e t).map (relabelBottom π) := by
  induction j generalizing b s with
  | zero => rfl
  | succ j ih => simp only [bottomExpressions,pivotExpression_relabel,childExpressions_relabel,
      ih,List.map_append]

@[simp] theorem indexedBottomExpressions_relabel (π : ι → κ) (k j : ℕ) (b : Bool) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) (i : Fin (2^j)) :
    indexedBottomExpressions k j b s (relabelExpressions π e) t i =
      relabelBottom π (indexedBottomExpressions k j b s e t i) := by
  simp only [indexedBottomExpressions,List.get_eq_getElem,bottomExpressions_relabel,List.getElem_map]
  rfl

@[simp] theorem periodExpression_relabel (π : ι → κ) (k : ℕ)
    (e : Expressions (ι:=ι) k 0) :
    periodExpression k (relabelExpressions π e) = relabel π (periodExpression k e) := by
  exact (relabel_finiteProductExpression π e).symm

@[simp] theorem evalBottom_relabel (π : ι → κ) (k : ℕ)
    (z : BottomExpression (ι:=ι) k) (a : κ → ℤ) :
    evalBottom k a (relabelBottom π z) = evalBottom k (fun i=>a (π i)) z := by
  simp only [evalBottom,relabelBottom,relabelExpressions_eval]

end Ostmann.Characters.TemplateOneSidedRelabel

end

end OAI
