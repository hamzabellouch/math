import OAI.NumberTheory.Ostmann.QuadraticCenter.PagePopulationDecay

namespace OAI

/-! # Endpoint products dominate the exceptional Page population -/

namespace Ostmann

open Filter

theorem eventual_page_pair_capacity (a C : ℝ) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop,
      C * (Real.exp L / L ^ 40) < (a * Real.exp (L / 2) / L ^ 6) ^ 2 := by
  have hp : ∀ᶠ L : ℝ in atTop, C / a ^ 2 < L ^ 28 :=
    (tendsto_pow_atTop (by norm_num : (28 : ℕ) ≠ 0)).eventually_gt_atTop (C / a ^ 2)
  filter_upwards [hp, eventually_gt_atTop (0 : ℝ)] with L hpower hL
  have hmain : C < a ^ 2 * L ^ 28 := by
    have hh := (div_lt_iff₀ (pow_pos ha 2)).mp hpower
    simpa only [mul_comm] using hh
  have he : Real.exp L = (Real.exp (L / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
  have hfactor : 0 < Real.exp L / L ^ 40 := div_pos (Real.exp_pos L) (pow_pos hL 40)
  have hmul := mul_lt_mul_of_pos_right hmain hfactor
  have hid : a ^ 2 * L ^ 28 * (Real.exp L / L ^ 40) =
      (a * Real.exp (L / 2) / L ^ 6) ^ 2 := by
    rw [he]
    field_simp
  rwa [hid] at hmul

end Ostmann

end OAI
