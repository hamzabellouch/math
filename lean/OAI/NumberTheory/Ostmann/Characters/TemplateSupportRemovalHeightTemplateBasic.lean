import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalHeightBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalSelected

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
open SymbolicHistory
attribute [local instance] Classical.propDecidable
variable {ι:Type*}

lemma expressionProduct_syntaxSize (es : List (Expr ι)) (M : ℕ)
    (h : ∀e∈es,e.syntaxSize≤M) :
    (HistoryReconstruction.expressionProduct es).syntaxSize≤(es.length+1)*(M+1) := by
  induction es with
  | nil => simp [HistoryReconstruction.expressionProduct,Expr.syntaxSize]
  | cons e es ih =>
    have he := h e (List.mem_cons_self)
    have ht := ih (fun q hq=>h q (List.mem_cons_of_mem e hq))
    simp only [HistoryReconstruction.expressionProduct,Expr.syntaxSize,List.length_cons]
    nlinarith

lemma finiteProductExpression_syntaxSize {α : Type*} [Fintype α]
    (e : α→Expr ι) (M : ℕ) (h : ∀i,(e i).syntaxSize≤M) :
    (finiteProductExpression e).syntaxSize≤(Fintype.card α+1)*(M+1) := by
  unfold finiteProductExpression
  have hh := expressionProduct_syntaxSize
    (List.ofFn (fun i:Fin (Fintype.card α)=>e ((Fintype.equivFin α).symm i))) M (by
      intro q hq
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
      exact h _)
  simpa only [List.length_ofFn] using hh

def expressionStepFactor (k j : ℕ) : ℕ :=
  2*(Fintype.card {i:(schedule k j).Slot // (schedule k j).IsCopied j i}+1)+7

lemma expressionStepFactor_pos (k j : ℕ) : 0 < expressionStepFactor k j := by
  unfold expressionStepFactor
  omega

lemma pivotExpression_syntaxSize (k j : ℕ) (e : Expressions (ι:=ι) k (j+1))
    (s v w : ℤ) (M : ℕ) (h : ∀i,(e i).syntaxSize≤M) :
    (pivotExpression k j e s v w).syntaxSize≤expressionStepFactor k j*(M+1) := by
  have hL := finiteProductExpression_syntaxSize
    (fun i:{i:(schedule k j).Slot // (schedule k j).IsCopied j i}=>e (.inl (i,false))) M (fun i=>h _)
  have hR := finiteProductExpression_syntaxSize
    (fun i:{i:(schedule k j).Slot // (schedule k j).IsCopied j i}=>e (.inl (i,true))) M (fun i=>h _)
  change (copiedExpression k j false e).syntaxSize≤_ at hL
  change (copiedExpression k j true e).syntaxSize≤_ at hR
  simp only [pivotExpression,Expr.syntaxSize,expressionStepFactor]
  nlinarith

lemma childExpressions_syntaxSize (k j : ℕ) (b : Bool)
    (e : Expressions (ι:=ι) k (j+1)) (s v w : ℤ) (M : ℕ)
    (h : ∀i,(e i).syntaxSize≤M) :
    ∀i,(childExpressions k j b e (pivotExpression k j e s v w) i).syntaxSize≤
      expressionStepFactor k j*(M+1) := by
  apply childExpressions_preserves k j b e (pivotExpression k j e s v w)
    (fun q=>q.syntaxSize≤expressionStepFactor k j*(M+1))
  · intro i
    have hh := h i
    have hg := expressionStepFactor_pos k j
    nlinarith
  · exact pivotExpression_syntaxSize k j e s v w M h

end Ostmann.Characters.Template

end

end OAI
