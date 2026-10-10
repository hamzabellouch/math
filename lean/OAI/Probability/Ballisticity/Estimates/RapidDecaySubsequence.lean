import Mathlib
import OAI.Probability.Ballisticity.Estimates.RapidDecay

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma RapidDecay.comp_strictMono {a : ℕ → ℝ} (ha : RapidDecay a) (ha0 : ∀ n, 0 ≤ a n)
    (f : ℕ → ℕ) (hf : StrictMono f) : RapidDecay (fun n => a (f n)) := by
  intro m
  apply ((ha m).comp_injective hf.injective).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (ha0 _))]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
    (by exact_mod_cast Nat.add_le_add_right (hf.id_le n) 1) m) (ha0 _)

lemma square_pred_strictMono : StrictMono (fun n : ℕ => (n+1)^2-1) := by
  intro n m hnm
  have h : (n+1)^2 < (m+1)^2 := by nlinarith
  change (n+1)^2-1 < (m+1)^2-1
  have hs : 1 ≤ (n+1)^2 := by nlinarith
  omega

end DirectionalTransience

end

end OAI
