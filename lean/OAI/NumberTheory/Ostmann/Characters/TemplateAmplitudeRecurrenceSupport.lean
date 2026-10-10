import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceStates
import OAI.NumberTheory.Ostmann.Characters.TemplateUnitSupport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

structure CurrentAtomSupport (k j : ℕ) (s : ℤ) (x : State k j) : Prop where
  root_ne_zero : s≠0
  positive : ∀i,0<x i
  pairwise : Pairwise (fun i h => IsCoprime (x i) (x h))
  root_coprime : ∀i,IsCoprime s (x i)

@[reducible] def TransferSupport (k : ℕ)
    (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop) :
    (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop
  | 0,s,x,t => CurrentAtomSupport k 0 s x ∧ extra 0 s x t
  | j+1,s,x,t => CurrentAtomSupport k (j+1) s x ∧
      NodeSupported k j x s t.1.1 t.1.2 (B j x) (V j x) ∧
      IntegerNodeSupport k j s t.1.1 t.1.2 x ∧ extra (j+1) s x t ∧
      TransferSupport k B V extra j t.1.1
        (childState k j true x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.1 ∧
      TransferSupport k B V extra j t.1.2
        (childState k j false x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.2

theorem TransferSupport.current {k j : ℕ} {B V extra s x t}
    (h : TransferSupport k B V extra j s x t) : CurrentAtomSupport k j s x := by
  cases j <;> exact h.1

theorem TransferSupport.unitSupported {k : ℕ} {B V extra} (j : ℕ) {s x t}
    (h : TransferSupport k B V extra j s x t) : UnitSupported k j s x t := by
  induction j generalizing s with
  | zero => trivial
  | succ j ih => exact ⟨h.2.2.1,ih h.2.2.2.2.1,ih h.2.2.2.2.2⟩

theorem TransferSupport.supported {k : ℕ} {B V extra} (j : ℕ) {s x t}
    (h : TransferSupport k B V extra j s x t) : Supported k B V j s x t := by
  induction j generalizing s with
  | zero => trivial
  | succ j ih => exact ⟨h.2.1,ih h.2.2.2.2.1,ih h.2.2.2.2.2⟩

theorem CurrentAtomSupport.source_copied_unit {k j : ℕ} (hj:j<k) (P : ℕ+)
    (h : CopiedState k j) (y : OutsideState k j) (s : ℤ)
    (hs : CurrentAtomSupport k j s (sourceState k j (P:ℤ) h y)) :
    IsUnit ((∏i,h i:ℤ):ZMod (P:ℕ)) := by
  have hc : IsCoprime (∏i,h i:ℤ) (P:ℤ) := by
    apply IsCoprime.prod_left
    intro i hi
    have hne : i.val≠(pivotSlot k j hj).val := by
      intro he
      have hh : (schedule k j).IsCopied j (pivotSlot k j hj).val := he ▸ i.property
      exact pivot_not_copied _ _ _ (pivotSlot k j hj).property hh
    have hh := hs.pairwise hne
    simpa only [sourceState,childState_copied,pairedState,ite_true,
      childState_pivot k j true _ _ _ (pivotSlot k j hj).property] using hh
  have hh := hc.map (Int.castRingHom (ZMod (P:ℕ)))
  change IsCoprime ((∏i,h i:ℤ):ZMod (P:ℕ)) ((P:ℤ):ZMod (P:ℕ)) at hh
  simpa only [Int.cast_natCast,ZMod.natCast_self,isCoprime_zero_right] using hh

end Ostmann.Characters.Template

end

end OAI
