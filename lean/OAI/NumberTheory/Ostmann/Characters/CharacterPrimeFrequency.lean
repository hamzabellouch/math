import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.Construction.ScheduledFrequencyBounds

namespace OAI

/-! # Natural character-frequency cutoffs lie below the actual prime ranges -/
namespace Ostmann
open Filter

/-- A fixed depth has a linear exponent, including the rounded bottom cutoff
with its original factor two in front of sqrt(m). -/
theorem transferErrorScale_linear_bound (k j : ℕ) (d m : ℝ)
    (hj : j ≤ k) (hd : 0 ≤ d) (hm : 1 ≤ m) :
    transferErrorScale (d * m) m j ≤ ((2 : ℝ) ^ k * d + 2 * (4 : ℝ) ^ k) * m := by
  have hs : Real.sqrt m ≤ m := (Real.sqrt_le_iff).mpr ⟨by linarith, by nlinarith⟩
  have htwo : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hj
  have hfour : (4 : ℝ) ^ j ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hj
  have hfirst := mul_le_mul_of_nonneg_right htwo (mul_nonneg hd (by linarith : 0 ≤ m))
  have hsecond := mul_le_mul hfour hs (Real.sqrt_nonneg _) (by positivity : (0 : ℝ) ≤ 4 ^ k)
  unfold transferErrorScale
  nlinarith only [hfirst, hsecond]

/-- This supplies both the prime-frequency separation and the finite powers
of the cutoff used for denominator removal in the selected energy estimate. -/
theorem eventual_natural_cutoff_power_lt (k r : ℕ) (d z α c : ℝ)
    (hd : 0 ≤ d) (_hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 1 ≤ m → m ≤ z * L → ∀ j ≤ k,
      (((naturalTransferCutoff (d * m) m j) ^ r : ℕ) : ℝ) <
        Real.exp (c * Real.exp (α * L)) := by
  let D := (2 : ℝ) ^ k * d + 2 * (4 : ℝ) ^ k
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb := ((isLittleO_pow_exp_pos_mul_atTop 1 hα).const_mul_left ((r : ℝ) * D * z)).bound
    (by positivity : 0 < c / 2)
  filter_upwards [hb] with L hL m hm hmL j hj
  have hlin : (r : ℝ) * D * z * L < c * Real.exp (α * L) := by
    have hh : |(r : ℝ) * D * z * L| ≤ c / 2 * Real.exp (α * L) := by
      simpa only [Real.norm_eq_abs, pow_one, abs_of_pos (Real.exp_pos _)] using hL
    have hn := le_abs_self ((r : ℝ) * D * z * L)
    nlinarith only [hh, hn, Real.exp_pos (α * L), hc]
  have hscale := transferErrorScale_linear_bound k j d m hj hd hm
  have hm' := mul_le_mul_of_nonneg_left hmL (mul_nonneg (Nat.cast_nonneg r) hD)
  have he : (r : ℝ) * transferErrorScale (d * m) m j < c * Real.exp (α * L) := by
    change transferErrorScale (d * m) m j ≤ D * m at hscale
    have hs := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg (α := ℝ) r)
    nlinarith only [hs, hm', hlin]
  calc
    _ = (naturalTransferCutoff (d * m) m j : ℝ) ^ r := by simp only [Nat.cast_pow]
    _ ≤ (Real.exp (transferErrorScale (d * m) m j)) ^ r :=
      pow_le_pow_left₀ (Nat.cast_nonneg _)
        (Nat.floor_le (Real.exp_pos _).le) r
    _ = Real.exp ((r : ℝ) * transferErrorScale (d * m) m j) := (Real.exp_nat_mul _ _).symm
    _ < _ := Real.exp_lt_exp.mpr he

theorem eventual_natural_cutoff_below_primes (k : ℕ) (d z α c : ℝ)
    (hd : 0 ≤ d) (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 1 ≤ m → m ≤ z * L →
      ∀ p : ℕ, Real.exp (c * Real.exp (α * L)) ≤ p →
        ∀ j ≤ k, naturalTransferCutoff (d * m) m j < p := by
  filter_upwards [eventual_natural_cutoff_power_lt k 1 d z α c hd hz hα hc] with L hL
  intro m hm hmL p hp j hj
  have hh := (hL m hm hmL j hj).trans_le hp
  simpa only [pow_one, Nat.cast_lt] using hh

end Ostmann

end OAI
