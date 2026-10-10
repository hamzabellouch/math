import OAI.NumberTheory.Ostmann.ZeroDensity.LogDerivativeSecondBound

namespace OAI

/-! # Vanishing second logarithmic derivative from subquadratic disk bounds -/

namespace Ostmann

open Complex Filter Metric
open scoped Topology

theorem deriv_logDeriv_eq_zero_of_disk_bounds (g : ℂ → ℂ)
    (hg : ∀ z, AnalyticAt ℂ g z) (hne : ∀ z, g z ≠ 0)
    (R A : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hA : ∀ n, 0 < A n)
    (hlog : ∀ n z, z ∈ ball 0 (R n) →
      Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ A n)
    (hsmall : Tendsto (fun n => A n / (R n) ^ 2) atTop (𝓝 0)) :
    deriv (logDeriv g) 0 = 0 := by
  have hb (n : ℕ) : ‖deriv (logDeriv g) 0‖ ≤ 16 * (A n / (R n) ^ 2) := by
    simpa only [mul_div_assoc] using deriv_logDeriv_norm_le_of_disk g (R n) (A n)
      (hR n) (hA n) (fun z _ => hg z) (fun z _ => hne z) (hlog n)
  have ht : Tendsto (fun n => 16 * (A n / (R n) ^ 2)) atTop (𝓝 0) := by
    simpa using hsmall.const_mul 16
  have hh : ‖deriv (logDeriv g) 0‖ ≤ 0 := ge_of_tendsto ht (Eventually.of_forall hb)
  exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))

end Ostmann

end OAI
