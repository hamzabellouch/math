import OAI.NumberTheory.Ostmann.Characters.TemplateCompositePivotSupportBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

structure CurrentRootSupport (k j : ℕ) (s : ℤ) (x : State k j) : Prop where
  root_ne_zero : s ≠ 0
  positive : ∀ i, 0 < x i
  root_coprime : ∀ i, IsCoprime s (x i)

theorem CurrentAtomSupport.toRootSupport {k j s x}
    (h : CurrentAtomSupport k j s x) : CurrentRootSupport k j s x :=
  ⟨h.root_ne_zero,h.positive,h.root_coprime⟩

@[reducible] def ReducedTransferSupport (k : ℕ)
    (B V : (j : ℕ) → State k (j+1) → ℤ)
    (extra : (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop) :
    (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop
  | 0,s,x,t => CurrentRootSupport k 0 s x ∧ extra 0 s x t
  | j+1,s,x,t => CurrentRootSupport k (j+1) s x ∧
      NodeSupported k j x s t.1.1 t.1.2 (B j x) (V j x) ∧
      IntegerNodeSupport k j s t.1.1 t.1.2 x ∧ extra (j+1) s x t ∧
      (∀ i : {i : (schedule k j).Slot // (schedule k j).IsOutside j i},
        IsCoprime (reconstructedPivot k j x s t.1.1 t.1.2) (x (.inr i))) ∧
      ReducedTransferSupport k B V extra j t.1.1
        (childState k j true x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.1 ∧
      ReducedTransferSupport k B V extra j t.1.2
        (childState k j false x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.2

theorem ReducedTransferSupport.current {k j : ℕ} {B V extra s x t}
    (h : ReducedTransferSupport k B V extra j s x t) : CurrentRootSupport k j s x := by
  cases j <;> exact h.1

theorem child_current_outside_coprime {k j : ℕ} (hj : j < k) {s P : ℤ}
    {x : State k (j+1)} {b : Bool}
    (h : CurrentAtomSupport k j s (childState k j b x P))
    (i : {i : (schedule k j).Slot // (schedule k j).IsOutside j i}) :
    IsCoprime P (x (.inr i)) := by
  have hne : (pivotSlot k j hj).val ≠ i.val := by
    intro he
    exact i.property.1 (he ▸ (pivotSlot k j hj).property)
  have hc := h.pairwise hne
  change IsCoprime (childState k j b x P (pivotSlot k j hj).val)
    (childState k j b x P i.val) at hc
  rw [childState_pivot k j b x P _ (pivotSlot k j hj).property,
    childState_outside k j b x P i] at hc
  exact hc

theorem transferSupport_iff_reduced {k : ℕ}
    (B V : (j : ℕ) → State k (j+1) → ℤ)
    (extra : (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (j : ℕ) (hj : j ≤ k) (s : ℤ) (x : State k j) (t : HistoryReconstruction.Tree j)
    (hpair : Pairwise (fun i h => IsCoprime (x i) (x h))) :
    TransferSupport k B V extra j s x t ↔ ReducedTransferSupport k B V extra j s x t := by
  induction j generalizing s with
  | zero =>
    constructor
    · intro h
      exact ⟨h.1.toRootSupport,h.2⟩
    · intro h
      exact ⟨⟨h.1.root_ne_zero,h.1.positive,hpair,h.1.root_coprime⟩,h.2⟩
  | succ j ih =>
    constructor
    · intro h
      refine ⟨h.1.toRootSupport,h.2.1,h.2.2.1,h.2.2.2.1,?_,?_,?_⟩
      · exact child_current_outside_coprime (by omega) h.2.2.2.2.1.current
      · exact (ih (by omega) _ _ _ h.2.2.2.2.1.current.pairwise).mp h.2.2.2.2.1
      · exact (ih (by omega) _ _ _ h.2.2.2.2.2.current.pairwise).mp h.2.2.2.2.2
    · intro h
      have hc (b : Bool) : Pairwise (fun i u => IsCoprime
          (childState k j b x (reconstructedPivot k j x s t.1.1 t.1.2) i)
          (childState k j b x (reconstructedPivot k j x s t.1.1 t.1.2) u)) := by
        apply childState_pairwise (by omega) b hpair _ h.2.2.2.2.1
        apply reconstructedPivot_coprime_copied hpair h.2.1.integral
        intro i
        cases b with
        | true =>
          have hh := h.2.2.2.2.2.1.current.root_coprime i.val
          simpa only [childState_copied, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] using hh
        | false =>
          have hh := h.2.2.2.2.2.2.current.root_coprime i.val
          simpa only [childState_copied, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] using hh
      refine ⟨⟨h.1.root_ne_zero,h.1.positive,hpair,h.1.root_coprime⟩,
        h.2.1,h.2.2.1,h.2.2.2.1,?_,?_⟩
      · exact (ih (by omega) _ _ _ (hc true)).mpr h.2.2.2.2.2.1
      · exact (ih (by omega) _ _ _ (hc false)).mpr h.2.2.2.2.2.2

end Ostmann.Characters.Template

end

end OAI
