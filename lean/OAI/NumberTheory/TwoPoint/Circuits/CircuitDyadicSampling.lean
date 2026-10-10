import OAI.NumberTheory.TwoPoint.Circuits.CircuitBernoulli
import Mathlib.Data.Nat.Log

namespace OAI

/-! Only logarithmically many Bernoulli parameters are needed to isolate a
zero among the inputs of an AND gate. The success constant 1/8 is sufficient
for the application's unspecified absolute circuit constants. -/

namespace TwoPointCorrelations

lemma exists_dyadic_single_hit (k z : ℕ) (hz : 0 < z) (hzk : z ≤ k) :
    ∃ a : ℕ, a ≤ Nat.log 2 k + 2 ∧
      1 / 8 ≤ (z : ℝ) * (1 / (2 : ℝ) ^ a) *
        (1 - 1 / (2 : ℝ) ^ a) ^ (z - 1) := by
  let l := Nat.log 2 z
  have hlog := Nat.log_mono_right (b := 2) hzk
  refine ⟨l + 2, by dsimp only [l]; omega, ?_⟩
  have hlow : (2 : ℝ) ^ l ≤ z := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt hz)
  have hhigh : (z : ℝ) < (2 : ℝ) ^ (l + 1) := by
    exact_mod_cast (Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2)
      (Nat.ne_of_gt hz)).mp (Nat.lt_succ_self l)
  have hpow : (2 : ℝ) ^ (l + 2) = 4 * (2 : ℝ) ^ l := by
    rw [pow_add]
    norm_num
    ring
  have hpow' : (2 : ℝ) ^ (l + 2) = 2 * (2 : ℝ) ^ (l + 1) := by
    rw [show l + 2 = (l + 1) + 1 by omega, pow_add]
    ring
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (l + 2) := by positivity
  apply single_hit_probability_lower z hz _ (by positivity)
  · rw [mul_one_div, div_le_iff₀ hpos, hpow']
    linarith
  · rw [mul_one_div, le_div_iff₀ hpos, hpow]
    linarith

end TwoPointCorrelations

end OAI
