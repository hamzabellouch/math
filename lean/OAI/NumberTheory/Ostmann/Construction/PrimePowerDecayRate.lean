import OAI.NumberTheory.Ostmann.Construction.SmoothMeanDecayRates

namespace OAI

/-! # Higher-prime-power errors at the sparse conductor scale -/
namespace Ostmann
open Filter

theorem eventual_prime_power_error (a A D : ℝ) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 1 ≤ Q →
      Real.log Q ≤ a * L * Real.exp ((9 / 10 : ℝ) * L) →
      (Real.exp (A * L) * (1 + (Q : ℝ) ^ 2)) *
        (2 * Real.sqrt (Real.exp (Real.exp L)) * Real.log (Real.exp (Real.exp L))) ≤
      Real.exp (Real.exp L) * Real.exp (-D * L) := by
  filter_upwards [eventual_conductor_exponential_decay a 2 4 (D + A + 1) ha (by norm_num)]
    with L hL Q hQ hlog
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hq2 : 1 + (Q : ℝ) ^ 2 ≤ 2 * (Q : ℝ) ^ 2 := by nlinarith
  have hd := hL (Real.log Q) (Real.log_nonneg hQ1) hlog
  have hpow : (Q : ℝ) ^ 2 = Real.exp (2 * Real.log Q) := by
    rw [show (2 : ℝ) * Real.log Q = Real.log Q + Real.log Q by ring,
      Real.exp_add, Real.exp_log hQ0, pow_two]
  calc
    _ ≤ (Real.exp (A * L) * (2 * (Q : ℝ) ^ 2)) *
        (2 * Real.sqrt (Real.exp (Real.exp L)) * Real.log (Real.exp (Real.exp L))) := by
      gcongr
      rw [Real.log_exp]
      positivity
    _ = (Real.exp (Real.exp L) * Real.exp ((A + 1) * L)) *
        (4 * Real.exp (2 * Real.log Q - Real.exp L / 2)) := by
      rw [hpow, Real.sqrt_eq_rpow, ← Real.exp_mul, Real.log_exp]
      have he : Real.exp (A * L) * Real.exp (2 * Real.log Q) *
          Real.exp (Real.exp L * (1 / 2)) * Real.exp L =
          Real.exp (Real.exp L) * Real.exp ((A + 1) * L) *
            Real.exp (2 * Real.log Q - Real.exp L / 2) := by
        simp only [← Real.exp_add]
        congr 1
        ring
      calc
        _ = 4 * (Real.exp (A * L) * Real.exp (2 * Real.log Q) *
            Real.exp (Real.exp L * (1 / 2)) * Real.exp L) := by ring
        _ = _ := by rw [he]; ring
    _ ≤ (Real.exp (Real.exp L) * Real.exp ((A + 1) * L)) *
        Real.exp (-(D + A + 1) * L) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem eventual_sparse_prime_below_half :
    ∀ᶠ L : ℝ in atTop, ∀ p : ℕ, 1 ≤ p →
      Real.log p ≤ Real.exp ((9 / 10 : ℝ) * L) →
      (p : ℝ) ≤ Real.exp (Real.exp L) / 2 := by
  filter_upwards [eventual_conductor_exponential_decay 1 1 2 0 (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hdec hL p hp hlog
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hd := hdec (Real.log p) (Real.log_nonneg hp1)
    (hlog.trans (by nlinarith [Real.exp_pos ((9 / 10 : ℝ) * L)]))
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul] at hd
  have hh := mul_le_mul_of_nonneg_right hd (Real.exp_nonneg (Real.exp L / 2))
  have hid : (2 * Real.exp (Real.log p - Real.exp L / 2)) * Real.exp (Real.exp L / 2) =
      2 * p := by
    rw [mul_assoc, ← Real.exp_add, sub_add_cancel, Real.exp_log hp0]
  rw [hid, one_mul] at hh
  have he : Real.exp (Real.exp L / 2) ≤ Real.exp (Real.exp L) :=
    Real.exp_le_exp.mpr (by linarith [Real.exp_pos L])
  linarith

theorem eventual_sparse_prime_error_margin (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, 2 * Real.exp (-10 * L) ≤ c / 4 * Real.exp (-L) := by
  filter_upwards [Real.tendsto_exp_neg_atTop_nhds_zero.eventually_le_const
    (show 0 < c / 8 by positivity), eventually_ge_atTop (0 : ℝ)] with L hh hL
  have h9 : Real.exp (-9 * L) ≤ c / 8 :=
    (Real.exp_le_exp.mpr (by linarith)).trans hh
  calc
    _ = (2 * Real.exp (-9 * L)) * Real.exp (-L) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (c / 4) * Real.exp (-L) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      linarith

end Ostmann

end OAI
