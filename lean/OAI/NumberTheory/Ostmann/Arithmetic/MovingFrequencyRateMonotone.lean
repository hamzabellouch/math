import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyBudget

namespace OAI

/-! # One frequency budget covers every depth of the finite schedule -/
namespace Ostmann

theorem movingFrequencyRate_nonneg (Bs BD Bz z : ℝ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hz : 1 ≤ z) (n : ℕ) :
    0 ≤ movingFrequencyRate Bs BD Bz z n := by
  have hl := Real.log_nonneg hz
  have hr := Real.log_nonneg (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n))
  unfold movingFrequencyRate
  positivity

theorem movingFrequencyRate_monotone (Bs BD Bz z : ℝ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hz : 1 ≤ z) :
    Monotone (movingFrequencyRate Bs BD Bz z) := by
  intro n k hnk
  have hp : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hnk
  have hl := Real.log_nonneg hz
  have hr := Real.log_nonneg (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n))
  have hlr := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ n) hp
  unfold movingFrequencyRate
  apply mul_le_mul hp
    (show Bs + 8 * Real.log z + BD + Bz * Real.log z + 2 / 5 * Real.log ((2 : ℝ) ^ n) + 2 ≤
      Bs + 8 * Real.log z + BD + Bz * Real.log z + 2 / 5 * Real.log ((2 : ℝ) ^ k) + 2 by linarith)
    (by positivity) (by positivity)

end Ostmann

end OAI
