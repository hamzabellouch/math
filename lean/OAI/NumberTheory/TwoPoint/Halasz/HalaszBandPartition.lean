import OAI.NumberTheory.TwoPoint.Halasz.HalaszLogBands
import Mathlib.Data.Nat.Log

namespace OAI

/-! A finite geometric partition of log(X/p), using base-two bands. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszBandIndex (y : ℝ) : ℕ := Nat.log 2 ⌊y / Real.log 2⌋₊

noncomputable def halaszBandScale (j : ℕ) : ℝ := Real.log 2 * 2 ^ j

lemma halasz_band_scale_bounds {y : ℝ} (hy : Real.log 2 ≤ y) :
    halaszBandScale (halaszBandIndex y) ≤ y ∧
      y < 2 * halaszBandScale (halaszBandIndex y) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hy0 : 0 ≤ y / Real.log 2 := div_nonneg (htwo.le.trans hy) htwo.le
  have hfloor : 1 ≤ ⌊y / Real.log 2⌋₊ :=
    (Nat.le_floor_iff hy0).mpr ((le_div_iff₀ htwo).mpr (by simpa using hy))
  have hlow := Nat.pow_log_le_self 2 (by omega : ⌊y / Real.log 2⌋₊ ≠ 0)
  have hhigh := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊y / Real.log 2⌋₊
  have hlowR : (2 : ℝ) ^ halaszBandIndex y ≤ (⌊y / Real.log 2⌋₊ : ℝ) := by
    exact_mod_cast hlow
  have hhighR : (⌊y / Real.log 2⌋₊ : ℝ) + 1 ≤ (2 : ℝ) ^ (halaszBandIndex y + 1) := by
    exact_mod_cast hhigh
  constructor
  · have h := hlowR.trans (Nat.floor_le hy0)
    have hh := (le_div_iff₀ htwo).mp h
    simpa only [halaszBandScale, mul_comm] using hh
  · have h := (Nat.lt_floor_add_one (y / Real.log 2)).trans_le hhighR
    have hh := (div_lt_iff₀ htwo).mp h
    simpa only [halaszBandScale, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hh

lemma halasz_band_index_mono {y Y : ℝ} (hyY : y ≤ Y) :
    halaszBandIndex y ≤ halaszBandIndex Y := by
  apply Nat.log_mono_right
  apply Nat.floor_mono
  exact div_le_div_of_nonneg_right hyY (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

noncomputable def halaszPrimeBandPart (P : Finset ℕ) (X : ℝ) (j : ℕ) : Finset ℕ :=
  P.filter (fun p : ℕ => halaszBandIndex (Real.log (X / p)) = j)

lemma halasz_prime_band_part_bounds (P : Finset ℕ) {X : ℝ} {j p : ℕ}
    (hP : ∀ p ∈ P, Real.log 2 ≤ Real.log (X / p))
    (hp : p ∈ halaszPrimeBandPart P X j) :
    halaszBandScale j ≤ Real.log (X / p) ∧ Real.log (X / p) < 2 * halaszBandScale j := by
  obtain ⟨hpP, hpj⟩ := mem_filter.mp hp
  simpa only [hpj] using halasz_band_scale_bounds (hP p hpP)

theorem halasz_prime_band_partition (P : Finset ℕ) {X Y : ℝ}
    (hP : ∀ p ∈ P, Real.log (X / p) ≤ Y) (a : ℕ → ℂ) :
    (∑ p ∈ P, a p) =
      ∑ j ∈ range (halaszBandIndex Y + 1), ∑ p ∈ halaszPrimeBandPart P X j, a p := by
  symm
  apply sum_fiberwise_of_maps_to
  intro p hp
  exact mem_range.mpr (Nat.lt_succ_of_le (halasz_band_index_mono (hP p hp)))

lemma halasz_band_scale_ge_log_two (j : ℕ) : Real.log 2 ≤ halaszBandScale j := by
  have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  simpa only [mul_one, halaszBandScale] using
    mul_le_mul_of_nonneg_left hp (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

end TwoPointCorrelations

end OAI
