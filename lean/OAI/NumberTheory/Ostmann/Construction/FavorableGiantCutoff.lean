import OAI.NumberTheory.Ostmann.Supply.TailSieveParameters

namespace OAI

/-! # A selected favorable block lies below the endpoint-test prime cutoff -/
namespace Ostmann
open Filter

theorem eventual_favorable_giant_cutoff :
    ∀ᶠ L : ℝ in atTop, ∀ lo : ℝ, lo ≤ Real.exp ((9 / 10 : ℝ) * L) →
      ⌈Real.exp (lo + 10 * Real.exp ((1 / 100 : ℝ) * L) + 3)⌉₊ ≤
        tailCollisionCutoff (Real.exp L) := by
  have hsmall := eventual_affine_log_le_rpow 5 (Real.log 2) (1 / 4) 1
    (by norm_num) (by norm_num) (by norm_num)
  simp only [Real.rpow_one] at hsmall
  filter_upwards [Real.tendsto_exp_atTop.eventually hsmall,
    Real.tendsto_exp_atTop.eventually (eventual_tailCollisionCutoff 0),
    eventually_ge_atTop (1000 : ℝ)] with L hsmall hcut hL lo hlo
  have hb : Real.exp ((9 / 10 : ℝ) * L) ≤ Real.exp L / 16 := by
    have h16 : 16 ≤ Real.exp ((1 / 10 : ℝ) * L) := by
      linarith [Real.add_one_le_exp ((1 / 10 : ℝ) * L)]
    have hh := mul_le_mul_of_nonneg_left h16 (Real.exp_nonneg ((9 / 10 : ℝ) * L))
    rw [← Real.exp_add, show (9 / 10 : ℝ) * L + (1 / 10 : ℝ) * L = L by ring] at hh
    linarith
  have hw : 10 * Real.exp ((1 / 100 : ℝ) * L) ≤ Real.exp ((9 / 10 : ℝ) * L) := by
    have h10 : 10 ≤ Real.exp ((89 / 100 : ℝ) * L) := by
      linarith [Real.add_one_le_exp ((89 / 100 : ℝ) * L)]
    have hh := mul_le_mul_of_nonneg_right h10 (Real.exp_nonneg ((1 / 100 : ℝ) * L))
    rw [← Real.exp_add, show (89 / 100 : ℝ) * L + (1 / 100 : ℝ) * L = (9 / 10) * L by ring] at hh
    exact hh
  have hb3 : 3 ≤ Real.exp ((9 / 10 : ℝ) * L) := by
    linarith [Real.add_one_le_exp ((9 / 10 : ℝ) * L)]
  have hQ := tailCollisionCutoff_bounds (Real.exp L) hcut.1 hcut.2.1
  have hlog : lo + 10 * Real.exp ((1 / 100 : ℝ) * L) + 3 ≤
      Real.log (tailCollisionCutoff (Real.exp L) : ℝ) := by
    linarith [hQ.2.2, Real.exp_pos L]
  apply Nat.ceil_le.mpr
  have hqp : (0 : ℝ) < tailCollisionCutoff (Real.exp L) := by exact_mod_cast hQ.1
  simpa only [Real.exp_log hqp] using Real.exp_le_exp.mpr hlog

end Ostmann

end OAI
