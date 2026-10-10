import OAI.NumberTheory.TwoPoint.Bounds.SieveGoldbachPairs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! The integer power cutoff needed to absorb the finite sieve remainder. -/

namespace TwoPointCorrelations

open Filter

lemma sieve_power_cutoff_log {x : ℝ} (hx : 1 ≤ x)
    (hlog : 16 * Real.log 2 ≤ Real.log x) (hlarge : 4 ≤ x ^ (1 / 8 : ℝ)) :
    let z := ⌊x ^ (1 / 8 : ℝ)⌋₊
    2 ≤ z ∧ (z : ℝ) ≤ x ^ (1 / 8 : ℝ) ∧
      Real.log x / 16 ≤ Real.log z ∧ Real.log z ≤ Real.log x := by
  let y := x ^ (1 / 8 : ℝ)
  let z := ⌊y⌋₊
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := Real.rpow_pos_of_pos hx0 _
  have hz2 : 2 ≤ z := (Nat.le_floor_iff hy0.le).mpr (by dsimp [y]; linarith)
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hzy : (z : ℝ) ≤ y := Nat.floor_le hy0.le
  have hyz : y / 2 ≤ (z : ℝ) := by
    have hf := Nat.lt_floor_add_one y
    change y < (z : ℝ) + 1 at hf
    dsimp [y] at *
    linarith
  have hlow := Real.log_le_log (div_pos hy0 (by norm_num)) hyz
  rw [Real.log_div hy0.ne' (by norm_num), show Real.log y = (1 / 8 : ℝ) * Real.log x from
    Real.log_rpow hx0 _] at hlow
  have hyx : y ≤ x := Real.rpow_le_self_of_one_le hx (by norm_num)
  exact ⟨hz2, hzy, by linarith, Real.log_le_log hz0 (hzy.trans hyx)⟩

lemma sieve_power_cutoff_error {x : ℝ} {z : ℕ} (hx : 1 ≤ x)
    (hlog : 1 ≤ Real.log x) (hz : (z : ℝ) ≤ x ^ (1 / 8 : ℝ))
    (hzlog : Real.log z ≤ Real.log x) (hzlog0 : 0 ≤ Real.log z)
    (hsmall : Real.log x ^ 6 ≤ (1 / 32 : ℝ) * x ^ (1 / 2 : ℝ)) :
    (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 + 2 * z ≤ x / Real.log x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hy1 : 1 ≤ x ^ (1 / 8 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hy0 : 0 ≤ x ^ (1 / 8 : ℝ) := (zero_le_one.trans hy1)
  have hz2 := pow_le_pow_left₀ (Nat.cast_nonneg z) hz 2
  have hlogs := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + Real.log z)
    (show 1 + Real.log z ≤ 2 * Real.log x by linarith) 4
  have h6 : Real.log x ^ 2 ≤ Real.log x ^ 6 := pow_le_pow_right₀ hlog (by norm_num)
  have hy2 : x ^ (1 / 8 : ℝ) ≤ (x ^ (1 / 8 : ℝ)) ^ 2 := by nlinarith
  have hterm : (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 + 2 * z ≤
      (x ^ (1 / 8 : ℝ)) ^ 2 * (16 * Real.log x ^ 4 + 2) := by
    have hp := mul_le_mul hz2 hlogs (by positivity) (by positivity)
    nlinarith
  have hpoly : (16 * Real.log x ^ 4 + 2) * Real.log x ^ 2 ≤ 18 * Real.log x ^ 6 := by
    nlinarith
  have hpow : (x ^ (1 / 8 : ℝ)) ^ 2 * x ^ (1 / 2 : ℝ) = x ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_mul_natCast hx0.le, ← Real.rpow_add hx0]
    norm_num
  apply (le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < Real.log x))).mpr
  calc
    _ ≤ ((x ^ (1 / 8 : ℝ)) ^ 2 * (16 * Real.log x ^ 4 + 2)) * Real.log x ^ 2 :=
      mul_le_mul_of_nonneg_right hterm (sq_nonneg _)
    _ = (x ^ (1 / 8 : ℝ)) ^ 2 * ((16 * Real.log x ^ 4 + 2) * Real.log x ^ 2) := by ring
    _ ≤ (x ^ (1 / 8 : ℝ)) ^ 2 * (18 * Real.log x ^ 6) :=
      mul_le_mul_of_nonneg_left hpoly (sq_nonneg _)
    _ ≤ (x ^ (1 / 8 : ℝ)) ^ 2 * (18 * ((1 / 32 : ℝ) * x ^ (1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsmall (by norm_num)) (sq_nonneg _)
    _ = (18 / 32 : ℝ) * x ^ (3 / 4 : ℝ) := by rw [← hpow]; ring
    _ ≤ x ^ (3 / 4 : ℝ) := by nlinarith [Real.rpow_nonneg hx0.le (3 / 4 : ℝ)]
    _ ≤ x := Real.rpow_le_self_of_one_le hx (by norm_num)

theorem sieve_power_cutoff_eventually (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ Real.log x ∧
      let z := ⌊x ^ (1 / 8 : ℝ)⌋₊
      2 ≤ z ∧ A ≤ Real.log z ∧ Real.log x ≤ 16 * Real.log z ∧
        (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 + 2 * z ≤ x / Real.log x ^ 2 := by
  have hl := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 (max (16 * A) (16 * Real.log 2))))
  have hy := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).eventually
    (eventually_ge_atTop (4 : ℝ))
  have hs := (isLittleO_log_rpow_rpow_atTop (6 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).bound (by norm_num : (0 : ℝ) < 1 / 32)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hl, hy, hs] with x hx hl hy hs
  have hlog : 1 ≤ Real.log x := (le_max_left _ _).trans hl
  have hA : 16 * A ≤ Real.log x := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have h2 : 16 * Real.log 2 ≤ Real.log x := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
  obtain ⟨hz, hzx, hlow, hhigh⟩ := sieve_power_cutoff_log hx h2 hy
  have hsmall : Real.log x ^ 6 ≤ (1 / 32 : ℝ) * x ^ (1 / 2 : ℝ) := by
    rw [show Real.log x ^ (6 : ℝ) = Real.log x ^ (6 : ℕ) from Real.rpow_natCast _ _] at hs
    simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ Real.log x ^ (6 : ℕ)),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) (1 / 2 : ℝ))] using hs
  refine ⟨hx, hlog, hz, by linarith, by linarith, ?_⟩
  exact sieve_power_cutoff_error hx hlog hzx hhigh
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ ⌊x ^ (1 / 8 : ℝ)⌋₊ by omega))) hsmall

end TwoPointCorrelations

end OAI
