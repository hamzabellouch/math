import OAI.NumberTheory.Ostmann.Characters.TemplateCompositePivotSupportActual
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalFamily

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
open SymbolicHistory TemplateSupportRemoval
attribute [local instance] Classical.propDecidable
variable {ι κ : Type*}

def outsidePivotExpressions (k : ℕ) (owner : κ) :
    (j : ℕ) → SampleOrigins k j κ → ℤ → Expressions (ι:=ι) k j →
      HistoryReconstruction.Tree j → List (Expr ι)
  | 0,_,_,_,_ => []
  | j+1,o,s,e,t =>
      let P := pivotExpression k j e s t.1.1 t.1.2
      (if ∃ i : {i : (schedule k j).Slot // (schedule k j).IsOutside j i},
          o.outside i = owner then [P] else []) ++
      (outsidePivotExpressions k owner j (o.child true) t.1.1
        (childExpressions k j true e P) t.2.1 ++
       outsidePivotExpressions k owner j (o.child false) t.1.2
        (childExpressions k j false e P) t.2.2)

def SelectedOutsideCoprime (k : ℕ) (owner : κ) (p : ℤ) :
    (j : ℕ) → SampleOrigins k j κ → ℤ → State k j → HistoryReconstruction.Tree j → Prop
  | 0,_,_,_,_ => True
  | j+1,o,s,x,t =>
      (∀ i : {i : (schedule k j).Slot // (schedule k j).IsOutside j i},
        o.outside i = owner → IsCoprime p (reconstructedPivot k j x s t.1.1 t.1.2)) ∧
      SelectedOutsideCoprime k owner p j (o.child true) t.1.1
        (childState k j true x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.1 ∧
      SelectedOutsideCoprime k owner p j (o.child false) t.1.2
        (childState k j false x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.2

theorem outsidePivotExpressions_mem (k : ℕ) (owner : κ) (j : ℕ)
    (o : SampleOrigins k j κ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (q : Expr ι)
    (hq : q ∈ outsidePivotExpressions k owner j o s e t) : q ∈ pivotExpressions k j s e t := by
  induction j generalizing s with
  | zero => exact False.elim (List.not_mem_nil hq)
  | succ j ih =>
    simp only [outsidePivotExpressions,List.mem_append] at hq
    rcases hq with hq | hq | hq
    · simp only [pivotExpressions,List.mem_cons]
      left
      split_ifs at hq with h
      · simpa using hq
      · exact False.elim (List.not_mem_nil hq)
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ih _ _ _ _ hq))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih _ _ _ _ hq))

theorem selectedOutsideCoprime_iff (k : ℕ) (owner : κ) (p : ℤ) (j : ℕ)
    (o : SampleOrigins k j κ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (a : ι → ℤ) :
    SelectedOutsideCoprime k owner p j o s (evalExpressions a e) t ↔
      ∀ q ∈ outsidePivotExpressions k owner j o s e t, IsCoprime p (q.integerEval a) := by
  induction j generalizing s with
  | zero => simp [SelectedOutsideCoprime,outsidePivotExpressions]
  | succ j ih =>
    let P := pivotExpression k j e s t.1.1 t.1.2
    have hl := ih (o.child true) t.1.1 (childExpressions k j true e P) t.2.1
    have hr := ih (o.child false) t.1.2 (childExpressions k j false e P) t.2.2
    simp only [childExpressions_eval,pivotExpression_eval,P] at hl hr
    simp only [SelectedOutsideCoprime,outsidePivotExpressions,List.forall_mem_append]
    rw [hl,hr]
    apply and_congr_left
    intro hrest
    by_cases h : ∃ i : {i : (schedule k j).Slot // (schedule k j).IsOutside j i},
        o.outside i = owner
    · rw [ite_eq_left h]
      simp only [List.forall_mem_cons,pivotExpression_eval]
      constructor
      · intro hn
        obtain ⟨i,hi⟩ := h
        exact ⟨hn i hi,fun q hq => False.elim (List.not_mem_nil hq)⟩
      · intro hn i hi
        exact hn.1
    · rw [ite_eq_right h]
      constructor
      · intro hn q hq
        exact False.elim (List.not_mem_nil hq)
      · intro hn i hi
        exact False.elim (h ⟨i,hi⟩)

def outsidePivotFamily (k : ℕ) (owner : κ) (j : ℕ) (o : SampleOrigins k j κ)
    (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) : Finset (Expr ι) :=
  (outsidePivotExpressions k owner j o s e t).toFinset

theorem outsidePivotFamily_mem_obstruction (k : ℕ) (owner : κ) (j : ℕ)
    (o : SampleOrigins k j κ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (q : Expr ι)
    (hq : q ∈ outsidePivotFamily k owner j o s e t) :
    q ∈ obstructionExpressions k j b s e t := by
  apply List.mem_append_left
  exact outsidePivotExpressions_mem k owner j o s e t q (List.mem_toFinset.mp hq)

theorem selectedOutsideCoprime_iff_family (k : ℕ) (owner : κ) (p : ℤ) (j : ℕ)
    (o : SampleOrigins k j κ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (a : ι → ℤ) :
    SelectedOutsideCoprime k owner p j o s (evalExpressions a e) t ↔
      ∀ q ∈ outsidePivotFamily k owner j o s e t, IsCoprime p (q.integerEval a) := by
  simpa only [outsidePivotFamily,List.mem_toFinset] using
    selectedOutsideCoprime_iff k owner p j o s e t a

end Ostmann.Characters.Template

end

end OAI
