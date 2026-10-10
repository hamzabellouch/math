import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationInterval

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem harmonic_le_twice_log_two_mul {q : ℕ} [NeZero q] :
    (harmonic q : ℝ) ≤ 2 * Real.log (2 * (q : ℝ)) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_neZero q
  have hl := Real.log_nonneg hq
  have ht := Real.log_two_gt_d9
  rw [Real.log_mul (by norm_num) (by positivity)]
  have hh := harmonic_le_one_add_log q
  linarith

theorem periodic_interval_twist_log_bound {q : ℕ} [NeZero q]
    (F : ZMod q → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ h, ‖normalizedCoefficient F h‖ ≤ A)
    (α : ℝ) (a : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, F ((a + (n : ℤ) : ℤ) : ZMod q) *
      weylPhase (((a : ℝ) + n) * α)‖ ≤
        4 * A * (N + q * Real.log (2 * (q : ℝ))) := by
  have h := periodic_interval_twist_bound F hA hcoeff α a N
  apply h.trans
  have hh := mul_le_mul_of_nonneg_left (harmonic_le_twice_log_two_mul (q := q))
    (show 0 ≤ 2 * (q : ℝ) by positivity)
  have hh' : 2 * (N : ℝ) + 2 * q * (harmonic q : ℝ) ≤
      4 * (N + q * Real.log (2 * (q : ℝ))) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hh' hA
  nlinarith

theorem interval_harmonic_factor_le_four_mul {q N : ℕ} [NeZero q]
    (hN : q ^ 2 ≤ N) :
    2 * (N : ℝ) + 2 * q * (harmonic q : ℝ) ≤ 4 * N := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_neZero q
  have hh : (harmonic q : ℝ) ≤ q := by
    have h1 := harmonic_le_one_add_log q
    have h2 := Real.log_le_sub_one_of_pos hq
    linarith
  have hsq : (q : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
  have hm := mul_le_mul_of_nonneg_left hh hq.le
  nlinarith

end Ostmann.QuadraticCenter

end

end OAI
