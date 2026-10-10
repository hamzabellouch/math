import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetFrequency
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedRelabelSampled
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportSurvivingExpressions

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportSurviving
open Template SymbolicHistory TemplateOneSidedBudget TemplateOneSidedRelabel
open HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

theorem expressionProduct_divisorsBelow (p : ℕ) (es : List (Expr ι))
    (he : ∀e∈es,e.DivisorsBelow p) :
    (HistoryReconstruction.expressionProduct es).DivisorsBelow p := by
  induction es with
  | nil => trivial
  | cons e es ih =>
    exact ⟨he e List.mem_cons_self,ih (fun q hq=>he q (List.mem_cons_of_mem _ hq))⟩

theorem finiteProductExpression_divisorsBelow (p : ℕ) {α : Type*} [Fintype α]
    (e : α→Expr ι) (he : ∀i,(e i).DivisorsBelow p) :
    (finiteProductExpression e).DivisorsBelow p := by
  apply expressionProduct_divisorsBelow
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact he _

theorem groupedExpressions_divisorsBelow (k j : ℕ) (width : Role→ℕ) (P : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j width)) (p : ℕ)
    (i : (schedule k j).Slot) :
    (groupedExpressions k j width P e i).DivisorsBelow p := by
  apply (relabel_divisorsBelow _ _ _).mpr
  apply childExpressions_preserves k j true _ (.fixed P) (fun q=>q.DivisorsBelow p)
  · intro z
    cases z with
    | inl z =>
      exact finiteProductExpression_divisorsBelow p
        (fun a : Fin (width ((schedule k j).role z.1.val)) =>
          Expr.atom (ι:=SurvivingPrimeIndex k j width) (.inl (e ⟨z.1,a⟩))) (fun _=>trivial)
    | inr z =>
      exact finiteProductExpression_divisorsBelow p
        (fun a : Fin (width ((schedule k j).role z.val)) =>
          Expr.atom (ι:=SurvivingPrimeIndex k j width) (.inr ⟨z,a⟩)) (fun _=>trivial)
  · trivial

theorem pivotExpression_divisorsBelow (k j : ℕ) (e : Expressions (ι:=ι) k (j+1))
    (p : ℕ) (he : ∀i,(e i).DivisorsBelow p) (s v w : ℤ) (hs : |s|<(p:ℤ)) :
    (pivotExpression k j e s v w).DivisorsBelow p := by
  have hc (b : Bool) : (copiedExpression k j b e).DivisorsBelow p :=
    finiteProductExpression_divisorsBelow p _ (fun _=>he _)
  exact ⟨⟨⟨trivial,hc false⟩,⟨trivial,hc true⟩⟩,hs⟩

theorem recursiveExpressions_divisorsBelow (k j : ℕ) (S : List Bool→Finset ℤ)
    (p : ℕ) (hS : ∀path s,s∈S path→|s|<(p:ℤ))
    (path : List Bool) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (he : ∀i,(e i).DivisorsBelow p)
    (ht : RangeSupported S j path s t) :
    (∀q∈pivotExpressions k j s e t,q.DivisorsBelow p) ∧
    (∀z∈bottomExpressions k j b s e t,∀i,(z.2.2 i).DivisorsBelow p) := by
  induction j generalizing path b s with
  | zero =>
    constructor
    · simp only [pivotExpressions,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    · intro z hz i
      have hz' : z=(b,s,e) := List.mem_singleton.mp hz
      subst z
      exact he i
  | succ j ih =>
    let P := pivotExpression k j e s t.1.1 t.1.2
    have hP : P.DivisorsBelow p := pivotExpression_divisorsBelow k j e p he s _ _ (hS path s ht.1)
    have hc (v : Bool) : ∀i,(childExpressions k j v e P i).DivisorsBelow p :=
      childExpressions_preserves k j v e P (fun q=>q.DivisorsBelow p) he hP
    have hl := ih (false::path) b t.1.1 (childExpressions k j true e P) t.2.1 (hc true) ht.2.1
    have hr := ih (true::path) (!b) t.1.2 (childExpressions k j false e P) t.2.2 (hc false) ht.2.2
    constructor
    · intro q hq
      change q∈P::(_++_) at hq
      rcases List.mem_cons.mp hq with hq|hq
      · subst q;exact hP
      · rcases List.mem_append.mp hq with hq|hq
        · exact hl.1 q hq
        · exact hr.1 q hq
    · intro z hz i
      change z∈(_++_) at hz
      rcases List.mem_append.mp hz with hz|hz
      · exact hl.2 z hz i
      · exact hr.2 z hz i

theorem obstructionExpressions_divisorsBelow (k j : ℕ) (S : List Bool→Finset ℤ)
    (p : ℕ) (hS : ∀path s,s∈S path→|s|<(p:ℤ))
    (path : List Bool) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (he : ∀i,(e i).DivisorsBelow p)
    (ht : RangeSupported S j path s t) :
    ∀q∈obstructionExpressions k j b s e t,q.DivisorsBelow p := by
  obtain ⟨hp,hb⟩ := recursiveExpressions_divisorsBelow k j S p hS path b s e t he ht
  intro q hq
  rcases List.mem_append.mp hq with hq|hq
  · exact hp q hq
  · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    exact finiteProductExpression_divisorsBelow p _ (hb z hz)

end Ostmann.Characters.TemplateOneSidedSupportSurviving

end

end OAI
