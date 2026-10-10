import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSupport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

def retainedHistoryWeight (k : ℕ) (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ)
    (j : ℕ) (s : ℤ) (x : State k j) (t : HistoryReconstruction.Tree j) : ℂ :=
  if TransferSupport k B V extra j s x t then weight k mask X Δ W j s x t else 0

theorem retainedHistoryWeight_support {k : ℕ} {B V extra mask X Δ W j s x t}
    (h : retainedHistoryWeight k B V extra mask X Δ W j s x t≠0) :
    TransferSupport k B V extra j s x t := by
  by_contra hn
  exact h (by simp only [retainedHistoryWeight,ite_eq_right hn])

def localTransferSupport (k j : ℕ) (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (s : ℤ) (x : State k (j+1)) (t : HistoryReconstruction.Tree (j+1)) : Prop :=
  CurrentAtomSupport k (j+1) s x ∧
    NodeSupported k j x s t.1.1 t.1.2 (B j x) (V j x) ∧
    IntegerNodeSupport k j s t.1.1 t.1.2 x ∧ extra (j+1) s x t

theorem retainedHistoryWeight_succ (k j : ℕ) (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ)
    (s : ℤ) (x : State k (j+1)) (t : HistoryReconstruction.Tree (j+1)) :
    retainedHistoryWeight k B V extra mask X Δ W (j+1) s x t =
      if localTransferSupport k j B V extra s x t ∧ mask (j+1) s x then
        let P := reconstructedPivot k j x s t.1.1 t.1.2
        retainedHistoryWeight k B V extra mask X Δ W j t.1.1 (childState k j true x P) t.2.1 *
          conj (retainedHistoryWeight k B V extra mask X Δ W j t.1.2 (childState k j false x P) t.2.2)
      else 0 := by
  classical
  unfold retainedHistoryWeight
  simp only [TransferSupport,weight,localTransferSupport]
  split_ifs <;> simp_all

theorem retainedHistoryWeight_norm_le (k : ℕ) (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ) (hX:0<X)
    (j : ℕ) (s : ℤ) (x : State k j) (t : HistoryReconstruction.Tree j) :
    ‖retainedHistoryWeight k B V extra mask X Δ W j s x t‖ ≤
      (Arithmetic.leafFourierBound*Real.exp ((-Δ+W)/2))^(2^j) := by
  unfold retainedHistoryWeight
  split_ifs
  · exact weight_norm_le k mask X Δ W hX j s x t
  · rw [norm_zero]
    exact pow_nonneg (mul_nonneg Arithmetic.leafFourierBound_pos.le (Real.exp_pos _).le) _

end Ostmann.Characters.Template

end

end OAI
