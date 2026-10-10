import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCanonicalGuardsCore
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCanonicalGuardsLeaf

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

theorem canonicalSourceWeightSupport_iff (k : ℕ)
    (B V : (j : ℕ) → State k (j+1) → ℤ)
    (extra : (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (J : ℤ) (X Δ W : ℝ) (j : ℕ) (s : ℤ) (x : State k j) (t : HistoryReconstruction.Tree j)
    (hc : TransferCoreSupport k B V extra j s x t) :
    WeightSupport k (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ W)) X Δ W j s x t ↔
      WeightSupport k (canonicalMask k (canonicalSourceLeafGuardData k J X Δ W)) X Δ W j s x t := by
  induction j generalizing s with
  | zero =>
    have hm := canonicalSourceLeafGuardData_zero k J s X Δ W x (fun b => hc.1.positive _)
    simp only [WeightSupport]
    exact and_congr_left (fun _ => hm.symm)
  | succ j ih =>
    simp only [WeightSupport]
    rw [canonicalSourceLeafGuardData_succ]
    exact and_congr_right (fun _ => and_congr
      (ih _ _ _ hc.2.2.2.2.1) (ih _ _ _ hc.2.2.2.2.2))

def canonicalSourceGuardList (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (X Δ W : ℝ) (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) : List (Guard ι) :=
  canonicalPivotCoreGuards k B V T W j s e t ++
    maskGuards k (canonicalSourceLeafGuardData k J X Δ W) j s e t

theorem canonicalSourceCoreWeight_eq_profiles (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (X Δ W : ℝ) (hX : 0 < X) (j : ℕ) (b : Bool) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) (a : ι → ℤ) :
    conjugateBy b (coreHistoryWeight k (fun l _ => B l) (fun l _ => V l)
      (canonicalHistoryExtra k (fun l => pivotWindow (T l) W))
      (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ W))
      X Δ W j s (evalExpressions a e) t) =
      if frequencyArithmetic k V j s (evalExpressions a e) t ∧
        (guardsHold (canonicalSourceGuardList k B V T J X Δ W j s e t) a ∧
          ∀i : Fin (2^j),(leafLowerGuard k X Δ W (indexedBottomExpressions k j b s e t i)).holds a)
      then ∏i : Fin (2^j),profileValue k X
        (evalBottom k a (indexedBottomExpressions k j b s e t i)) else 0 := by
  have hcore := canonicalPivotCoreSupport_iff k B V T W j s e t a
  unfold coreHistoryWeight
  by_cases hc : TransferCoreSupport k (fun l _ => B l) (fun l _ => V l)
      (canonicalHistoryExtra k (fun l => pivotWindow (T l) W)) j s (evalExpressions a e) t
  · rw [ite_eq_left hc,weight_eq_fixed_symbolic_profiles_indicator k _ X Δ W hX j b s e t a,
      canonicalSourceWeightSupport_iff k _ _ _ J X Δ W j s _ t hc,
      weightSupport_iff_fixed_leaf_guards k (canonicalSourceLeafGuardData k J X Δ W)
        X Δ W j b s e t a]
    have hh := hcore.mp hc
    simp only [canonicalSourceGuardList,guardsHold_append,hh.1,hh.2,true_and]
    split_ifs <;> rfl
  · rw [ite_eq_right hc]
    have hn : ¬(frequencyArithmetic k V j s (evalExpressions a e) t ∧
        (guardsHold (canonicalSourceGuardList k B V T J X Δ W j s e t) a ∧
          ∀i : Fin (2^j),(leafLowerGuard k X Δ W (indexedBottomExpressions k j b s e t i)).holds a)) := by
      intro h
      exact hc (hcore.mpr ⟨h.1,(guardsHold_append _ _ _).mp h.2.1 |>.1⟩)
    rw [ite_eq_right hn]
    simp [conjugateBy]

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
