import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-! The source cutoff beats the enlarged width and every fixed polynomial. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert

/-- The two exponents are exactly the manuscript's `0.9` and `0.97`.
This is the numerical small-time input to compact-witness transfer. -/
theorem eventually_short_time_decay (p : ℝ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop,
      2 * C * L ^ p * Real.exp (L ^ (9 / 10 : ℝ) - L ^ (97 / 100 : ℝ)) ≤ 1 / 2 := by
  have hlog := (isLittleO_log_rpow_atTop (r := 97 / 100) (by norm_num)).const_mul_left p
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 100)).eventually_ge_atTop 3,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 97 / 100)).eventually_ge_atTop
      (3 * |Real.log (4 * C)|),
    hlog.bound (by norm_num : (0 : ℝ) < 1 / 3)] with L hL hgap hconstant hlogL
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hr : 0 ≤ L ^ (97 / 100 : ℝ) := Real.rpow_nonneg hL0.le _
  have hs : 0 ≤ L ^ (9 / 10 : ℝ) := Real.rpow_nonneg hL0.le _
  simp only [Real.norm_eq_abs, abs_of_nonneg hr] at hlogL
  have hpower : L ^ (97 / 100 : ℝ) = L ^ (9 / 10 : ℝ) * L ^ (7 / 100 : ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hslow : 3 * L ^ (9 / 10 : ℝ) ≤ L ^ (97 / 100 : ℝ) := by
    rw [hpower]
    nlinarith [mul_le_mul_of_nonneg_left hgap hs]
  have hexponent : Real.log (4 * C) + Real.log L * p +
      (L ^ (9 / 10 : ℝ) - L ^ (97 / 100 : ℝ)) ≤ 0 := by
    have hlogabs := le_abs_self (p * Real.log L)
    have hcabs := le_abs_self (Real.log (4 * C))
    nlinarith
  have hfour : 4 * C * L ^ p * Real.exp (L ^ (9 / 10 : ℝ) - L ^ (97 / 100 : ℝ)) ≤ 1 := by
    calc
      _ = Real.exp (Real.log (4 * C) + Real.log L * p +
          (L ^ (9 / 10 : ℝ) - L ^ (97 / 100 : ℝ))) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity : 0 < 4 * C),
          Real.rpow_def_of_pos hL0]
      _ ≤ 1 := Real.exp_le_one_iff.mpr hexponent
  nlinarith

/-- The actual source inequalities `m≤2 exp(L^0.9)` and
`tau≤exp(-L^0.97)` imply the exact transfer hypothesis uniformly over
all top lengths below `tau`. -/
theorem eventually_transfer_small_time (p : ℝ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ m tau ell : ℝ,
      0 ≤ m → m ≤ 2 * Real.exp (L ^ (9 / 10 : ℝ)) →
      0 ≤ tau → tau ≤ Real.exp (-(L ^ (97 / 100 : ℝ))) →
      0 ≤ ell → ell ≤ tau → C * L ^ p * m * ell ≤ 1 / 2 := by
  by_cases hzero : C = 0
  · subst C
    exact Filter.Eventually.of_forall (by intros; norm_num)
  have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
  filter_upwards [eventually_short_time_decay p hCpos, eventually_ge_atTop (0 : ℝ)]
    with L hdecay hL m tau ell hm hmb ht htb he heb
  have hLp : 0 ≤ L ^ p := Real.rpow_nonneg hL _
  calc
    C * L ^ p * m * ell ≤ C * L ^ p * m * tau :=
      mul_le_mul_of_nonneg_left heb (by positivity)
    _ ≤ C * L ^ p * (2 * Real.exp (L ^ (9 / 10 : ℝ))) *
        Real.exp (-(L ^ (97 / 100 : ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hmb (by positivity)) htb ht (by positivity)
    _ = 2 * C * L ^ p * Real.exp (L ^ (9 / 10 : ℝ) - L ^ (97 / 100 : ℝ)) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ 1 / 2 := hdecay

end LipschitzHilbert

end

end OAI
