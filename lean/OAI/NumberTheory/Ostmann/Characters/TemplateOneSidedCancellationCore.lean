import OAI.NumberTheory.Ostmann.Characters.TemplateCompositePivotSupportFamilyCore
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationFrequencySupport
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedLeafProfilesGuards

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

theorem canonicalCoreSupport_iff (k : ℕ) (B V : ℕ → ℤ)
    (g : (j : ℕ) → ℤ → List (Guard (schedule k j).Slot)) (j : ℕ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) (a : ι → ℤ) :
    TransferCoreSupport k (fun j _ => B j) (fun j _ => V j)
      (fun j s x _ => canonicalMask k g j s x) j s (evalExpressions a e) t ↔
      frequencyArithmetic k V j s (evalExpressions a e) t ∧
        guardsHold (historyGuards k B V g j s e t) a := by
  induction j generalizing s with
  | zero =>
    simp only [TransferCoreSupport,frequencyArithmetic,historyGuards,guardsHold_append,
      guardsHold_substitute,canonicalMask]
    rw [currentRootSupport_iff]
    tauto
  | succ j ih =>
    let P := pivotExpression k j e s t.1.1 t.1.2
    have hl := ih t.1.1 (childExpressions k j true e P) t.2.1
    have hr := ih t.1.2 (childExpressions k j false e P) t.2.2
    simp only [childExpressions_eval,pivotExpression_eval,P,canonicalMask] at hl hr
    simp only [TransferCoreSupport,frequencyArithmetic,historyGuards,guardsHold_append,
      guardsHold_substitute,canonicalMask]
    rw [currentRootSupport_iff,nodeSupported_iff,hl,hr]
    tauto

def coreHistoryWeight (k : ℕ)
    (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ)
    (j : ℕ) (s : ℤ) (x : State k j) (t : HistoryReconstruction.Tree j) : ℂ :=
  if TransferCoreSupport k B V extra j s x t then weight k mask X Δ W j s x t else 0

def coreGuardList (k : ℕ) (B V : ℕ → ℤ)
    (g m : (j:ℕ) → ℤ → List (Guard (schedule k j).Slot))
    (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) :
    List (Guard ι) := historyGuards k B V g j s e t ++ maskGuards k m j s e t

theorem coreHistoryWeight_eq_profiles (k : ℕ) (B V : ℕ → ℤ)
    (g m : (j:ℕ) → ℤ → List (Guard (schedule k j).Slot)) (X Δ W : ℝ) (hX : 0 < X)
    (j : ℕ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (a : ι → ℤ) :
    conjugateBy b (coreHistoryWeight k (fun j _ => B j) (fun j _ => V j)
      (fun j s x _ => canonicalMask k g j s x) (canonicalMask k m)
      X Δ W j s (evalExpressions a e) t) =
      if frequencyArithmetic k V j s (evalExpressions a e) t ∧
        (guardsHold (coreGuardList k B V g m j s e t) a ∧
          ∀ i : Fin (2^j),(leafLowerGuard k X Δ W (indexedBottomExpressions k j b s e t i)).holds a)
      then ∏ i : Fin (2^j),profileValue k X
        (evalBottom k a (indexedBottomExpressions k j b s e t i)) else 0 := by
  have hc := canonicalCoreSupport_iff k B V g j s e t a
  have hw := weightSupport_iff_fixed_leaf_guards k m X Δ W j b s e t a
  unfold coreHistoryWeight
  simp only [hc,coreGuardList,guardsHold_append]
  by_cases h : frequencyArithmetic k V j s (evalExpressions a e) t ∧
      guardsHold (historyGuards k B V g j s e t) a
  · rw [ite_eq_left h,weight_eq_fixed_symbolic_profiles_indicator k _ X Δ W hX j b s e t a]
    simp only [hw,h.1,h.2,true_and]
  · rw [ite_eq_right h]
    have hn : ¬(frequencyArithmetic k V j s (evalExpressions a e) t ∧
        ((guardsHold (historyGuards k B V g j s e t) a ∧
          guardsHold (maskGuards k m j s e t) a) ∧
        ∀ i : Fin (2^j),(leafLowerGuard k X Δ W (indexedBottomExpressions k j b s e t i)).holds a)) := by
      intro hh
      exact h ⟨hh.1,hh.2.1.1⟩
    rw [ite_eq_right hn]
    simp [conjugateBy]

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
