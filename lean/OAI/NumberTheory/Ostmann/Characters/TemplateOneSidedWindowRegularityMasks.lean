import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedWindowRegularity

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateOneSidedBudget
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

theorem maskGuards_good (k : ℕ) (V : ℕ → ℤ)
    (g : (j : ℕ) → ℤ → List (Guard (schedule k j).Slot))
    (hg : ∀ j s a q, q ∈ g j s → HistoryReconstruction.Good a q.expression)
    (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (a : ι → ℤ)
    (he : ∀ i, HistoryReconstruction.Good a (e i))
    (hf : frequencyArithmetic k V j s (evalExpressions a e) t) :
    ∀ q ∈ maskGuards k g j s e t, HistoryReconstruction.Good a q.expression := by
  induction j generalizing s with
  | zero =>
    intro q hq
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
    exact substitute_good e r.expression a he (hg 0 s _ r hr)
  | succ j ih =>
    let P := pivotExpression k j e s t.1.1 t.1.2
    have hp : HistoryReconstruction.Good a P :=
      pivotExpression_good_of_nodeArithmetic k j e _ _ _ _ a he hf.2.1
    have hgl := childExpressions_preserves k j true e P _ he hp
    have hgr := childExpressions_preserves k j false e P _ he hp
    have hfl : frequencyArithmetic k V j t.1.1
        (evalExpressions a (childExpressions k j true e P)) t.2.1 := by
      rw [childExpressions_eval,pivotExpression_eval]
      exact hf.2.2.2.1
    have hfr : frequencyArithmetic k V j t.1.2
        (evalExpressions a (childExpressions k j false e P)) t.2.2 := by
      rw [childExpressions_eval,pivotExpression_eval]
      exact hf.2.2.2.2
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
      exact substitute_good e r.expression a he (hg (j+1) s _ r hr)
    rcases List.mem_append.mp hq with hq | hq
    · exact ih _ _ _ hgl hfl q hq
    · exact ih _ _ _ hgr hfr q hq

theorem maskCoordinateWindowGuards_good (k : ℕ) (V : ℕ → ℤ)
    (w : (j : ℕ) → ℤ → Fin (coordinateWindowExpressions k j).length → Option SourceWindow)
    (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (a : ι → ℤ)
    (he : ∀ i, HistoryReconstruction.Good a (e i))
    (hf : frequencyArithmetic k V j s (evalExpressions a e) t) :
    ∀ q ∈ maskGuards k (fun l u => coordinateWindowGuards k l (w l u)) j s e t,
      HistoryReconstruction.Good a q.expression :=
  maskGuards_good k V _
    (fun l u x => coordinateWindowGuards_good k l (w l u) x) j s e t a he hf

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
