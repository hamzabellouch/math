import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetGuards

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedBudget
open SymbolicHistory Template TemplateOneSidedCancellation
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

structure SourceWindow where
  lower : ℝ
  upper : ℝ
  strictUpper : Bool

def compileWindow (e : Expr ι) : Option SourceWindow → List (Guard ι)
  | none => []
  | some w => [windowGuards e w.lower w.upper w.strictUpper false,
      windowGuards e w.lower w.upper w.strictUpper true]

theorem compileWindow_length (e : Expr ι) (w : Option SourceWindow) :
    (compileWindow e w).length ≤ 2 := by cases w <;> simp [compileWindow]

theorem compileWindow_expression (e : Expr ι) (w : Option SourceWindow)
    (q : Guard ι) (hq : q∈compileWindow e w) : q.expression=e := by
  cases w with
  | none => simp only [compileWindow,List.not_mem_nil] at hq
  | some w =>
    simp only [compileWindow,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl <;> rfl

def compileWindows (es : List (Expr ι × Option SourceWindow)) : List (Guard ι) :=
  es.flatMap (fun q=>compileWindow q.1 q.2)

theorem compileWindows_length (es : List (Expr ι × Option SourceWindow)) :
    (compileWindows es).length ≤ 2*es.length := by
  induction es with
  | nil => simp [compileWindows]
  | cons e es ih =>
    change (compileWindow e.1 e.2 ++ compileWindows es).length ≤ _
    rw [List.length_append,List.length_cons]
    nlinarith [compileWindow_length e.1 e.2]

theorem compileWindows_size (es : List (Expr ι × Option SourceWindow)) (D : ℕ)
    (he : ∀q∈es,q.1.syntaxSize ≤ D) :
    ∀q∈compileWindows es,q.expression.syntaxSize ≤ D := by
  intro q hq
  obtain ⟨e,he',hq⟩ := List.mem_flatMap.mp hq
  rw [compileWindow_expression _ _ _ hq]
  exact he e he'

def coordinateWindowExpressions (k j : ℕ) : List (Expr (schedule k j).Slot) :=
  List.ofFn (fun i : Fin (Fintype.card (schedule k j).Slot)=>
    Expr.atom ((Fintype.equivFin (schedule k j).Slot).symm i)) ++
      [finiteProductExpression (fun i : (schedule k j).Slot=>Expr.atom i)]

theorem coordinateWindowExpressions_length (k j : ℕ) :
    (coordinateWindowExpressions k j).length=Fintype.card (schedule k j).Slot+1 := by
  simp only [coordinateWindowExpressions,List.length_append,List.length_ofFn,
    List.length_cons,List.length_nil]

theorem coordinateWindowExpressions_size (k j : ℕ) :
    ∀q∈coordinateWindowExpressions k j,q.syntaxSize ≤ 2*(Fintype.card (schedule k j).Slot+1) := by
  intro q hq
  rcases List.mem_append.mp hq with hq|hq
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    change 1 ≤ _
    omega
  · have hq' := List.mem_singleton.mp hq
    subst q
    have hh := finiteProductExpression_syntaxSize (fun i : (schedule k j).Slot=>Expr.atom i) 1 (fun _=>le_rfl)
    simpa only [show 1+1=2 by rfl,Nat.mul_comm] using hh

def nodeWindowExpressions (k j : ℕ) (s v w : ℤ) : List (Expr (schedule k (j+1)).Slot) :=
  let e : Expressions (ι:=(schedule k (j+1)).Slot) k (j+1) := fun i=>Expr.atom i
  [copiedExpression k j false e,copiedExpression k j true e,pivotExpression k j e s v w]

theorem nodeWindowExpressions_length (k j : ℕ) (s v w : ℤ) :
    (nodeWindowExpressions k j s v w).length=3 := rfl

theorem nodeWindowExpressions_size (k j : ℕ) (s v w : ℤ) :
    ∀q∈nodeWindowExpressions k j s v w,q.syntaxSize ≤ 2*expressionStepFactor k j := by
  let e : Expressions (ι:=(schedule k (j+1)).Slot) k (j+1) := fun i=>Expr.atom i
  have hc (b : Bool) : (copiedExpression k j b e).syntaxSize ≤ 2*expressionStepFactor k j := by
    have hh := finiteProductExpression_syntaxSize
      (fun i : {i:(schedule k j).Slot // (schedule k j).IsCopied j i}=>e (.inl (i,b))) 1 (fun _=>le_rfl)
    change (copiedExpression k j b e).syntaxSize ≤ _ at hh
    unfold expressionStepFactor
    nlinarith
  have hp := pivotExpression_syntaxSize k j e s v w 1 (fun _=>le_rfl)
  intro q hq
  simp only [nodeWindowExpressions,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  · exact hc false
  · exact hc true
  · simpa only [show 1+1=2 by rfl,Nat.mul_comm] using hp

def candidateWindowGuards (es : List (Expr ι)) (w : Fin es.length → Option SourceWindow) :
    List (Guard ι) := compileWindows (List.ofFn (fun i=> (es.get i,w i)))

theorem candidateWindowGuards_length (es : List (Expr ι)) (w : Fin es.length → Option SourceWindow) :
    (candidateWindowGuards es w).length ≤ 2*es.length := by
  simpa only [candidateWindowGuards,List.length_ofFn] using
    compileWindows_length (List.ofFn (fun i=> (es.get i,w i)))

theorem candidateWindowGuards_size (es : List (Expr ι)) (w : Fin es.length → Option SourceWindow)
    (D : ℕ) (he : ∀q∈es,q.syntaxSize ≤ D) :
    ∀q∈candidateWindowGuards es w,q.expression.syntaxSize ≤ D := by
  apply compileWindows_size
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact he _ (List.get_mem _ i)

end Ostmann.Characters.TemplateOneSidedBudget

end

end OAI
