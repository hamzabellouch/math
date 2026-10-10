import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationCanonical
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedLeafProfiles

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

def leafLowerGuard (k : ℕ) (X Δ W : ℝ) (z : BottomExpression (ι:=ι) k) : Guard ι :=
  ⟨periodExpression k z.2.2,Real.exp (Real.log X+Δ-W),true,false⟩

def bottomPeriodSupport (k : ℕ) (X Δ W : ℝ) (z : BottomDatum k) : Prop :=
  0 < (period k 0 z.2.2:ℝ) ∧ Real.log X+Δ-W ≤ Real.log (period k 0 z.2.2:ℝ)

theorem leafLowerGuard_holds (k : ℕ) (X Δ W : ℝ)
    (z : BottomExpression (ι:=ι) k) (a : ι → ℤ) :
    (leafLowerGuard k X Δ W z).holds a ↔ bottomPeriodSupport k X Δ W (evalBottom k a z) := by
  simp only [leafLowerGuard,Guard.holds,ite_true,Bool.false_eq_true,ite_false,
    periodExpression_eval,bottomPeriodSupport,evalBottom]
  constructor
  · intro h
    have hp := (Real.exp_pos (Real.log X+Δ-W)).trans_le h
    exact ⟨hp,(Real.le_log_iff_exp_le hp).mpr h⟩
  · rintro ⟨hp,h⟩
    exact (Real.le_log_iff_exp_le hp).mp h

theorem weightSupport_iff_masks_bottomPeriods (k : ℕ)
    (g : (j:ℕ) → ℤ → List (Guard (schedule k j).Slot)) (X Δ W : ℝ)
    (j : ℕ) (b : Bool) (s : ℤ) (x : State k j) (t : HistoryReconstruction.Tree j) :
    WeightSupport k (canonicalMask k g) X Δ W j s x t ↔
      masksOnHistory k g j s x t ∧
        ∀ z ∈ bottomData k j b s x t, bottomPeriodSupport k X Δ W z := by
  induction j generalizing b s with
  | zero =>
    simp only [WeightSupport,masksOnHistory,bottomData,List.mem_singleton,forall_eq,
      bottomPeriodSupport]
  | succ j ih =>
    have hl := ih b t.1.1
      (childState k j true x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.1
    have hr := ih (!b) t.1.2
      (childState k j false x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.2
    simp only [WeightSupport,masksOnHistory,bottomData,List.mem_append,or_imp,forall_and,hl,hr]
    tauto

theorem weightSupport_iff_fixed_leaf_guards (k : ℕ)
    (g : (j:ℕ) → ℤ → List (Guard (schedule k j).Slot)) (X Δ W : ℝ)
    (j : ℕ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (a : ι → ℤ) :
    WeightSupport k (canonicalMask k g) X Δ W j s (evalExpressions a e) t ↔
      guardsHold (maskGuards k g j s e t) a ∧
        ∀ i : Fin (2^j), (leafLowerGuard k X Δ W (indexedBottomExpressions k j b s e t i)).holds a := by
  rw [weightSupport_iff_masks_bottomPeriods k g X Δ W j b s _ t]
  apply and_congr (maskGuards_holds k g j s e t a).symm
  rw [← bottomExpressions_eval k j b s e t a,List.forall_mem_map]
  rw [← indexedBottomExpressions_forall k j b s e t
    (fun z => bottomPeriodSupport k X Δ W (evalBottom k a z))]
  apply forall_congr'
  intro i
  exact (leafLowerGuard_holds k X Δ W _ a).symm

theorem retainedHistoryWeight_eq_compiled_leaf_profiles (k : ℕ) (B V : ℕ → ℤ)
    (g m : (j:ℕ) → ℤ → List (Guard (schedule k j).Slot)) (X Δ W : ℝ) (hX : 0 < X)
    (j : ℕ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (a : ι → ℤ) :
    conjugateBy b (retainedHistoryWeight k (fun j _ => B j) (fun j _ => V j)
      (fun j s x _ => canonicalMask k g j s x) (canonicalMask k m)
      X Δ W j s (evalExpressions a e) t) =
      if (historyArithmetic k B V j s (evalExpressions a e) t ∧
          guardsHold (historyGuards k B V g j s e t) a) ∧
        (guardsHold (maskGuards k m j s e t) a ∧
          ∀ i : Fin (2^j), (leafLowerGuard k X Δ W (indexedBottomExpressions k j b s e t i)).holds a)
      then ∏ i : Fin (2^j), profileValue k X
        (evalBottom k a (indexedBottomExpressions k j b s e t i)) else 0 := by
  rw [retainedHistoryWeight_eq_fixed_profiles k _ _ _ _ X Δ W hX j b s e t a,
    canonicalTransfer_iff k B V g j s e t a,
    weightSupport_iff_fixed_leaf_guards k m X Δ W j b s e t a]
  split_ifs <;> rfl

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
