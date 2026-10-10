import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.Construction.BalancedHalfInitialStatistic

namespace OAI

/-! # A depth-independent exponential rate for the actual endpoint statistic -/
namespace Ostmann
open Filter

/-- The number of top and compensation roles changes only the threshold.
The exponential coefficient remains independent of their number. -/
theorem eventual_balanced_endpoint_rate (r : ℕ) (a c δ A : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ (L Y X E : ℝ) (n : ℕ),
      L ≤ m → 0 < Y → Y ≤ Real.exp L → 0 ≤ X → n ≤ m + r →
      a * Real.sqrt X / Y ^ 3 ≤ E →
      Real.sqrt X * Real.exp (-(2 * A + 2 * Real.log 2 + 4) * m) ≤
        E * (c * (Real.exp (-A * m) * (1 / 2 : ℝ) ^ n * δ) ^ 2) := by
  have hfixed : 0 < a * c * δ ^ 2 * Real.exp (-(2 * Real.log 2) * r) := by positivity
  have hf := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_le_const hfixed
  filter_upwards [hf] with m hm L Y X E n hL hY hYL _hX hn hE
  change Real.exp (-(m : ℝ)) ≤ a * c * δ ^ 2 * Real.exp (-(2 * Real.log 2) * r) at hm
  have hn' : (n : ℝ) ≤ (m : ℝ) + r := by exact_mod_cast hn
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hYupper : Y ^ 3 ≤ Real.exp (3 * (m : ℝ)) := by
    calc
      _ ≤ (Real.exp L) ^ 3 := pow_le_pow_left₀ hY.le hYL 3
      _ = Real.exp (3 * L) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hYinv : Real.exp (-3 * (m : ℝ)) ≤ (Y ^ 3)⁻¹ := by
    have hi := inv_anti₀ (pow_pos hY 3) hYupper
    simpa only [Real.exp_neg, neg_mul] using hi
  have hElower : a * Real.sqrt X * Real.exp (-3 * (m : ℝ)) ≤ E := by
    apply le_trans _ hE
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hYinv (by positivity)
  have hhalf : ((1 / 2 : ℝ) ^ n) ^ 2 = Real.exp (-(2 * Real.log 2) * n) := by
    have he : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [he, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hpow : (Real.exp (-A * (m : ℝ))) ^ 2 = Real.exp (-(2 * A) * m) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hcoef : Real.exp (-(2 * A + 2 * Real.log 2 + 4) * (m : ℝ)) ≤
      a * c * δ ^ 2 * Real.exp (-3 * (m : ℝ)) * Real.exp (-(2 * A) * m) *
        Real.exp (-(2 * Real.log 2) * n) := by
    calc
      _ = Real.exp (-(m : ℝ)) * Real.exp (-(3 + 2 * A + 2 * Real.log 2) * m) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ (a * c * δ ^ 2 * Real.exp (-(2 * Real.log 2) * r)) *
          Real.exp (-(3 + 2 * A + 2 * Real.log 2) * m) :=
        mul_le_mul_of_nonneg_right hm (Real.exp_nonneg _)
      _ = a * c * δ ^ 2 * Real.exp (-3 * (m : ℝ)) * Real.exp (-(2 * A) * m) *
          Real.exp (-(2 * Real.log 2) * ((m : ℝ) + r)) := by
        simp only [mul_assoc, ← Real.exp_add]
        congr 2
        ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith only [hn', hlog2])) (by positivity)
  calc
    _ ≤ Real.sqrt X * (a * c * δ ^ 2 * Real.exp (-3 * (m : ℝ)) *
        Real.exp (-(2 * A) * m) * Real.exp (-(2 * Real.log 2) * n)) :=
      mul_le_mul_of_nonneg_left hcoef (Real.sqrt_nonneg X)
    _ = (a * Real.sqrt X * Real.exp (-3 * (m : ℝ))) *
        (c * (Real.exp (-A * m) * (1 / 2 : ℝ) ^ n * δ) ^ 2) := by
      rw [mul_pow, mul_pow, hpow, hhalf]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hElower (by positivity)

end Ostmann

end OAI
