import Mathlib.NumberTheory.Chebyshev
import OAI.NumberTheory.Ostmann.Endpoint
import OAI.NumberTheory.Ostmann.Setup

namespace OAI

namespace Ostmann.Preliminaries
open Filter

theorem eventually_log_counting_error (N : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      (N : ℝ) * Real.log x + Real.log ((x : ℝ) + 1) ≤ Real.log 2 / 2 * x := by
  let ε : ℝ := Real.log 2 / (2 * ((N : ℝ) + 2))
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : 0 < ε := div_pos hlog (by positivity)
  have hx : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hx1 : Tendsto (fun x : ℕ => (x : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 hx
  have hsmall := Real.isLittleO_log_id_atTop.bound he
  filter_upwards [hx.eventually hsmall, hx1.eventually hsmall, eventually_ge_atTop 2] with x h1 h2 hx2
  have hx2r : (2 : ℝ) ≤ x := by exact_mod_cast hx2
  have hxn : (0 : ℝ) ≤ x := by positivity
  have hlogx : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by linarith)
  have hlogx1 : 0 ≤ Real.log ((x : ℝ) + 1) := Real.log_nonneg (by linarith)
  simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg hlogx, abs_of_nonneg hxn] at h1
  simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg hlogx1,
    abs_of_nonneg (show 0 ≤ (x : ℝ) + 1 by positivity)] at h2
  have hscale : ε * ((N : ℝ) + 2) = Real.log 2 / 2 := by dsimp [ε]; field_simp
  have hn : (0 : ℝ) ≤ N := by positivity
  calc
    (N : ℝ) * Real.log x + Real.log ((x : ℝ) + 1) ≤
        (N : ℝ) * (ε * x) + ε * ((x : ℝ) + 1) := by gcongr
    _ ≤ ε * ((N : ℝ) + 2) * x := by nlinarith
    _ = _ := by rw [hscale]

theorem eventually_primeCounting_lower :
    ∀ᶠ x : ℕ in atTop,
      Real.log 2 / 2 * (x : ℝ) / Real.log x ≤ Nat.primeCounting x := by
  filter_upwards [eventually_log_counting_error 0, eventually_ge_atTop 2] with x he hx
  have hx2 : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hl : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
  have hc := Chebyshev.pi_ge x
  apply le_trans _ hc
  apply div_le_div_of_nonneg_right _ hl.le
  simp only [Nat.cast_zero, zero_mul, zero_add] at he
  nlinarith

theorem eventually_count_product_lower (d : Decomposition) :
    ∀ᶠ x : ℕ in atTop,
      Real.log 2 / 2 * (x : ℝ) / Real.log x ≤
        (countUpTo d.A x : ℝ) * countUpTo d.B x := by
  obtain ⟨N, hN⟩ := d.eventuallyEqual.primeCounting_le
  filter_upwards [eventually_log_counting_error N, eventually_ge_atTop 2] with x he hx
  have hx2 : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hl : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
  have hc := Chebyshev.pi_ge x
  have hn : (Nat.primeCounting x : ℝ) ≤
      (countUpTo d.A x : ℝ) * countUpTo d.B x + N := by exact_mod_cast hN x
  have hmain : (x : ℝ) * Real.log 2 - Real.log ((x : ℝ) + 1) ≤
      ((countUpTo d.A x : ℝ) * countUpTo d.B x + N) * Real.log x :=
    (div_le_iff₀ hl).mp (hc.trans hn)
  apply (div_le_iff₀ hl).mpr
  nlinarith

end Ostmann.Preliminaries

end OAI
