import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWeight
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedLeafProfilesBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
open SymbolicHistory
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

theorem weightSupport_of_weight_ne_zero (k : ℕ) (mask : (j:ℕ) → ℤ → State k j → Prop)
    (X Δ W : ℝ) (j : ℕ) (s : ℤ) (x : State k j) (t : HistoryReconstruction.Tree j)
    (h : weight k mask X Δ W j s x t ≠ 0) : WeightSupport k mask X Δ W j s x t := by
  induction j generalizing s with
  | zero =>
    by_cases hm : mask 0 s x
    · rw [weight,ite_eq_left hm] at h
      by_cases hp : 0 < (period k 0 x:ℝ) ∧ Real.log X+Δ-W ≤ Real.log (period k 0 x:ℝ)
      · exact ⟨hm,hp⟩
      · exact (h (by simp only [leafWeight,ite_eq_right hp])).elim
    · exact (h (by simp only [weight,ite_eq_right hm])).elim
  | succ j ih =>
    by_cases hm : mask (j+1) s x
    · rw [weight,ite_eq_left hm] at h
      refine ⟨hm,ih _ _ _ (mul_ne_zero_iff.mp h).1,ih _ _ _ ?_⟩
      intro hz
      exact (mul_ne_zero_iff.mp h).2 (by rw [hz,map_zero])
    · exact (h (by simp only [weight,ite_eq_right hm])).elim

theorem weight_eq_zero_of_not_weightSupport (k : ℕ)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ) (j : ℕ)
    (s : ℤ) (x : State k j) (t : HistoryReconstruction.Tree j)
    (h : ¬WeightSupport k mask X Δ W j s x t) : weight k mask X Δ W j s x t = 0 := by
  by_contra hn
  exact h (weightSupport_of_weight_ne_zero k mask X Δ W j s x t hn)

theorem weight_eq_fixed_symbolic_profiles_indicator (k : ℕ)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ) (hX : 0 < X)
    (j : ℕ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (a : ι → ℤ) :
    conjugateBy b (weight k mask X Δ W j s (evalExpressions a e) t) =
      if WeightSupport k mask X Δ W j s (evalExpressions a e) t then
        ∏ i : Fin (2^j), profileValue k X
          (evalBottom k a (indexedBottomExpressions k j b s e t i)) else 0 := by
  by_cases h : WeightSupport k mask X Δ W j s (evalExpressions a e) t
  · rw [ite_eq_left h]
    exact weight_eq_fixed_symbolic_profiles k mask X Δ W hX j b s e t a h
  · rw [ite_eq_right h,weight_eq_zero_of_not_weightSupport k mask X Δ W j s _ t h]
    simp only [conjugateBy,map_zero,ite_self]

theorem retainedHistoryWeight_eq_fixed_profiles (k : ℕ)
    (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ) (hX : 0 < X)
    (j : ℕ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (a : ι → ℤ) :
    conjugateBy b (retainedHistoryWeight k B V extra mask X Δ W j s (evalExpressions a e) t) =
      if TransferSupport k B V extra j s (evalExpressions a e) t ∧
        WeightSupport k mask X Δ W j s (evalExpressions a e) t then
        ∏ i : Fin (2^j), profileValue k X
          (evalBottom k a (indexedBottomExpressions k j b s e t i)) else 0 := by
  unfold retainedHistoryWeight
  by_cases h : TransferSupport k B V extra j s (evalExpressions a e) t
  · simp only [h,true_and]
    exact weight_eq_fixed_symbolic_profiles_indicator k mask X Δ W hX j b s e t a
  · simp only [h,false_and,ite_false,conjugateBy,map_zero,ite_self]

end Ostmann.Characters.Template

end

end OAI
