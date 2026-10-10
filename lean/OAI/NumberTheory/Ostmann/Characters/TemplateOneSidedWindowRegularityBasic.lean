import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetWindows
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationFrequencySupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateOneSidedBudget
attribute [local instance] Classical.propDecidable
variable {ι κ : Type*}

theorem substitute_good (e : κ → Expr ι) (q : Expr κ) (a : ι → ℤ)
    (he : ∀ i, HistoryReconstruction.Good a (e i))
    (hq : HistoryReconstruction.Good (fun i => (e i).integerEval a) q) :
    HistoryReconstruction.Good a (substitute e q) :=
  ⟨substitute_valid e q (fun i => (he i).1) hq.1,
    substitute_integral e q a (fun i => (he i).2) hq.2⟩

theorem coordinateWindowExpressions_good (k j : ℕ) (a : State k j) :
    ∀ q ∈ coordinateWindowExpressions k j, HistoryReconstruction.Good a q := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact ⟨trivial,trivial⟩
  · have hq' := List.mem_singleton.mp hq
    subst q
    exact finiteProductExpression_good _ a (fun _ => ⟨trivial,trivial⟩)

theorem candidateWindowGuards_good (es : List (Expr ι))
    (w : Fin es.length → Option SourceWindow) (a : ι → ℤ)
    (he : ∀ q ∈ es, HistoryReconstruction.Good a q) :
    ∀ q ∈ candidateWindowGuards es w, HistoryReconstruction.Good a q.expression := by
  intro q hq
  obtain ⟨u,hu,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
  rw [compileWindow_expression _ _ _ hq]
  exact he _ (List.get_mem es i)

def coordinateWindowGuards (k j : ℕ)
    (w : Fin (coordinateWindowExpressions k j).length → Option SourceWindow) :
    List (Guard (schedule k j).Slot) := candidateWindowGuards (coordinateWindowExpressions k j) w

theorem coordinateWindowGuards_good (k j : ℕ)
    (w : Fin (coordinateWindowExpressions k j).length → Option SourceWindow)
    (a : State k j) :
    ∀ q ∈ coordinateWindowGuards k j w, HistoryReconstruction.Good a q.expression :=
  candidateWindowGuards_good _ w a (coordinateWindowExpressions_good k j a)

theorem coordinateWindowGuards_length (k j : ℕ)
    (w : Fin (coordinateWindowExpressions k j).length → Option SourceWindow) :
    (coordinateWindowGuards k j w).length ≤ 2*(Fintype.card (schedule k j).Slot+1) := by
  simpa only [coordinateWindowGuards,coordinateWindowExpressions_length] using
    candidateWindowGuards_length (coordinateWindowExpressions k j) w

theorem coordinateWindowGuards_size (k j : ℕ)
    (w : Fin (coordinateWindowExpressions k j).length → Option SourceWindow) :
    ∀ q ∈ coordinateWindowGuards k j w,
      q.expression.syntaxSize ≤ 2*(Fintype.card (schedule k j).Slot+1) :=
  candidateWindowGuards_size _ w _ (coordinateWindowExpressions_size k j)

theorem positiveGuards_good (k j : ℕ) (e : Expressions (ι:=ι) k j) (a : ι → ℤ)
    (he : ∀ i, HistoryReconstruction.Good a (e i)) :
    ∀ q ∈ positiveGuards k j e, HistoryReconstruction.Good a q.expression := by
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact he _

theorem nodeGuards_good (k j : ℕ) (e : Expressions (ι:=ι) k (j+1))
    (s v w B V : ℤ) (a : ι → ℤ) (he : ∀ i, HistoryReconstruction.Good a (e i))
    (hn : NodeArithmetic k j (evalExpressions a e) s v w V) :
    ∀ q ∈ nodeGuards k j e s v w B V, HistoryReconstruction.Good a q.expression := by
  have hc := copiedExpression_good k j false e a he
  have hp := pivotExpression_good_of_nodeArithmetic k j e s v w V a he hn
  intro q hq
  simp only [nodeGuards,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact hc
  · exact hp
  · exact hp
  · exact hc

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
