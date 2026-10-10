import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedLeafProfilesBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedWindowRegularityBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedWindowRegularityValue

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateOneSidedBudget
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

theorem historyGuards_good (k : ℕ) (B V : ℕ → ℤ)
    (g : (j : ℕ) → ℤ → List (Guard (schedule k j).Slot))
    (hg : ∀ j s a q, q ∈ g j s → HistoryReconstruction.Good a q.expression)
    (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (a : ι → ℤ)
    (he : ∀ i, HistoryReconstruction.Good a (e i))
    (hf : frequencyArithmetic k V j s (evalExpressions a e) t) :
    ∀ q ∈ historyGuards k B V g j s e t, HistoryReconstruction.Good a q.expression := by
  induction j generalizing s with
  | zero =>
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact positiveGuards_good k 0 e a he q hq
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
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
    · exact positiveGuards_good k (j+1) e a he q hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
      exact substitute_good e r.expression a he (hg (j+1) s _ r hr)
    rcases List.mem_append.mp hq with hq | hq
    · exact nodeGuards_good k j e _ _ _ _ _ a he hf.2.1 q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ih _ _ _ hgl hfl q hq
    · exact ih _ _ _ hgr hfr q hq

theorem historyCoordinateWindowGuards_good (k : ℕ) (B V : ℕ → ℤ)
    (w : (j : ℕ) → ℤ → Fin (coordinateWindowExpressions k j).length → Option SourceWindow)
    (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (a : ι → ℤ)
    (he : ∀ i, HistoryReconstruction.Good a (e i))
    (hf : frequencyArithmetic k V j s (evalExpressions a e) t) :
    ∀ q ∈ historyGuards k B V (fun l u => coordinateWindowGuards k l (w l u)) j s e t,
      HistoryReconstruction.Good a q.expression :=
  historyGuards_good k B V _
    (fun l u x => coordinateWindowGuards_good k l (w l u) x) j s e t a he hf

theorem bottomExpressions_good_of_frequencyArithmetic (k : ℕ) (V : ℕ → ℤ) (j : ℕ)
    (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (a : ι → ℤ)
    (he : ∀ i, HistoryReconstruction.Good a (e i))
    (hf : frequencyArithmetic k V j s (evalExpressions a e) t) :
    ∀ z ∈ bottomExpressions k j b s e t, ∀ i, HistoryReconstruction.Good a (z.2.2 i) := by
  induction j generalizing b s with
  | zero =>
    intro z hz
    have hz' := List.mem_singleton.mp hz
    subst z
    exact he
  | succ j ih =>
    let P := pivotExpression k j e s t.1.1 t.1.2
    have hp : HistoryReconstruction.Good a P :=
      pivotExpression_good_of_nodeArithmetic k j e _ _ _ _ a he hf.2.1
    have hfl : frequencyArithmetic k V j t.1.1
        (evalExpressions a (childExpressions k j true e P)) t.2.1 := by
      rw [childExpressions_eval,pivotExpression_eval]
      exact hf.2.2.2.1
    have hfr : frequencyArithmetic k V j t.1.2
        (evalExpressions a (childExpressions k j false e P)) t.2.2 := by
      rw [childExpressions_eval,pivotExpression_eval]
      exact hf.2.2.2.2
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact ih b _ _ _ (childExpressions_preserves k j true e P _ he hp) hfl z hz
    · exact ih (!b) _ _ _ (childExpressions_preserves k j false e P _ he hp) hfr z hz

theorem indexedBottomExpressions_period_good_of_frequencyArithmetic
    (k : ℕ) (V : ℕ → ℤ) (j : ℕ) (b : Bool) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) (a : ι → ℤ)
    (he : ∀ i, HistoryReconstruction.Good a (e i))
    (hf : frequencyArithmetic k V j s (evalExpressions a e) t) (i : Fin (2^j)) :
    HistoryReconstruction.Good a
      (periodExpression k (indexedBottomExpressions k j b s e t i).2.2) :=
  finiteProductExpression_good _ a
    (bottomExpressions_good_of_frequencyArithmetic k V j b s e t a he hf _
      (indexedBottomExpressions_mem k j b s e t i))

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
