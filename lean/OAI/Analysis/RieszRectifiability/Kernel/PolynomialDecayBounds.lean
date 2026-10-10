import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.TemperedHeightWeights

namespace OAI

namespace RieszRectifiability

noncomputable section

theorem polynomial_decay_from_uniform_and_far_bound {d : ℕ} (q : ℕ)
    (f : Ambient d → ℂ) (U D : ℝ) (hU : 0 ≤ U) (hD : 0 ≤ D)
    (hu : ∀ x, ‖f x‖ ≤ U)
    (hd : ∀ x, 0 < ‖x‖ → ‖f x‖ ≤ D / ‖x‖ ^ q) (x : Ambient d) :
    ‖f x‖ ≤ (2 ^ q * (U + D)) * polynomialDecay q x := by
  rw [polynomialDecay, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖x‖) q)).2
  by_cases hx : 1 ≤ ‖x‖
  · have hp : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
    have hb : (1 + ‖x‖) ^ q ≤ (2 * ‖x‖) ^ q :=
      pow_le_pow_left₀ (by positivity) (by linarith) q
    calc
      _ ≤ (D / ‖x‖ ^ q) * (2 * ‖x‖) ^ q :=
        mul_le_mul (hd x hp) hb (by positivity) (div_nonneg hD (by positivity))
      _ = 2 ^ q * D := by
        rw [mul_pow]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith : D ≤ U + D) (by positivity)
  · have hb : (1 + ‖x‖) ^ q ≤ (2 : ℝ) ^ q :=
      pow_le_pow_left₀ (by positivity) (by linarith) q
    calc
      _ ≤ U * 2 ^ q := mul_le_mul (hu x) hb (by positivity) hU
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (by linarith : U ≤ U + D)
          (by positivity : 0 ≤ (2 : ℝ) ^ q)
        simpa only [mul_comm] using! hh

end

end RieszRectifiability

end OAI
