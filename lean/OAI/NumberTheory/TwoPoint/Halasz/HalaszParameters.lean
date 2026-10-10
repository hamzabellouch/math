import OAI.NumberTheory.TwoPoint.Halasz.HalaszBandSummation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-! The logarithmic truncation height and integer smoothing length used
in the grouped Perron estimate. -/

namespace TwoPointCorrelations

open Filter

lemma halasz_eventually_numeric_scale (B : ℝ) :
    ∀ᶠ x : ℝ in atTop, 3 ≤ x ∧ 1 ≤ Real.log (Real.log x) ∧
      2 ≤ Real.log x ^ 4 ∧ Real.log x ^ 16 ≤ x / 2 ∧ B ≤ Real.log x ^ 8 := by
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 16)).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 2 B))
  have hloglog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_ge_atTop (3 : ℝ), hlog, hloglog, hsmall] with x hx hl hll hs
  have hl2 : 2 ≤ Real.log x := (le_max_left _ _).trans hl
  have hl1 : 1 ≤ Real.log x := by linarith
  dsimp only [id] at hs
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ Real.log x) 16),
    Real.norm_eq_abs, abs_of_pos (by linarith : 0 < x)] at hs
  refine ⟨hx, hll, ?_, by linarith, ?_⟩
  · exact hl2.trans (le_self_pow₀ hl1 (by norm_num : (4 : ℕ) ≠ 0))
  · exact ((le_max_right _ _).trans hl).trans (le_self_pow₀ hl1 (by norm_num : (8 : ℕ) ≠ 0))

lemma halasz_smoothing_integer {N : ℕ} (hN : 2 ≤ N)
    (hlog : 2 ≤ Real.log (N : ℝ) ^ 4) (hsmall : Real.log (N : ℝ) ^ 4 ≤ N) :
    let m := ⌈(N : ℝ) / Real.log (N : ℝ) ^ 4⌉₊
    0 < m ∧ m ≤ N ∧ (N : ℝ) / Real.log (N : ℝ) ^ 4 ≤ m ∧
      (m : ℝ) ≤ 2 * ((N : ℝ) / Real.log (N : ℝ) ^ 4) ∧
      ((N : ℝ) + 1 / 2) / m ≤ 2 * Real.log (N : ℝ) ^ 4 := by
  let L := Real.log (N : ℝ) ^ 4
  let m := ⌈(N : ℝ) / L⌉₊
  have hL : 0 < L := by dsimp [L]; linarith
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hratio : 1 ≤ (N : ℝ) / L := (le_div_iff₀ hL).mpr (by simpa [L] using hsmall)
  have hratioHigh : (N : ℝ) / L ≤ (N : ℝ) / 2 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog
  have hmlo : (N : ℝ) / L ≤ m := Nat.le_ceil _
  have hmhi : (m : ℝ) < (N : ℝ) / L + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmp : (0 : ℝ) < m := by linarith
  have hmNat : 0 < m := by exact_mod_cast hmp
  have hmN : m ≤ N := by exact_mod_cast (show (m : ℝ) ≤ N by linarith)
  refine ⟨hmNat, hmN, hmlo, by linarith, ?_⟩
  apply (div_le_iff₀ hmp).mpr
  have hmul : (N : ℝ) ≤ (m : ℝ) * L := (div_le_iff₀ hL).mp hmlo
  dsimp [L] at hmul ⊢
  nlinarith

end TwoPointCorrelations

end OAI
