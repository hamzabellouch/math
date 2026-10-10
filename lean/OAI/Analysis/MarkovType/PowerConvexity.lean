import OAI.Analysis.MarkovType.RenormingBasic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

namespace OAI

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem uniformConvex_of_symmetric_power
    (p : Seminorm ℝ E) (q c : ℝ) (hq : 0 < q) (hc : 0 < c) (hc_one : c ≤ 1)
    (hpower : ∀ x y : E, (p x) ^ q + c * (p y) ^ q ≤
      ((p (x + y)) ^ q + (p (x - y)) ^ q) / 2) : UniformConvex p := by
  intro ε hε hε_two
  let d : ℝ := c * (ε / 2) ^ q
  have hd : 0 < d := mul_pos hc (Real.rpow_pos_of_pos (half_pos hε) q)
  have hehalf : ε / 2 ≤ 1 := by linarith only [hε_two]
  have hepow : (ε / 2) ^ q ≤ 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (half_pos hε).le hehalf hq.le
  have hd_one : d ≤ 1 := by
    calc
      c * (ε / 2) ^ q ≤ c * 1 := mul_le_mul_of_nonneg_left hepow hc.le
      _ ≤ 1 := by simpa only [mul_one] using hc_one
  let r : ℝ := 1 - d
  have hr : 0 ≤ r := sub_nonneg.mpr hd_one
  have hr_one : r < 1 := by dsimp [r]; linarith only [hd]
  have hrpow : r ^ (1 / q) < 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_lt_rpow hr hr_one (one_div_pos.mpr hq)
  let δ : ℝ := 1 - r ^ (1 / q)
  refine ⟨δ, sub_pos.mpr hrpow, ?_⟩
  intro x y hx hy hsep
  let z : E := (1 / 2 : ℝ) • (x + y)
  let w : E := (1 / 2 : ℝ) • (x - y)
  have hz : z + w = x := by dsimp [z, w]; module
  have hw : z - w = y := by dsimp [z, w]; module
  have hs := hpower z w
  rw [hz, hw] at hs
  have hxpow : (p x) ^ q ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (apply_nonneg p x) hx hq.le
  have hypow : (p y) ^ q ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (apply_nonneg p y) hy hq.le
  have hwvalue : p w = p (x - y) / 2 := by
    dsimp [w]
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  have hwlower : ε / 2 ≤ p w := by rw [hwvalue]; linarith only [hsep]
  have hwpow := Real.rpow_le_rpow (half_pos hε).le hwlower hq.le
  have hcwpow := mul_le_mul_of_nonneg_left hwpow hc.le
  have hzbound : (p z) ^ q ≤ r := by
    dsimp [r, d]
    linarith only [hs, hxpow, hypow, hcwpow]
  have hroot : p z ≤ r ^ (1 / q) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (apply_nonneg p z) q)
      hzbound (one_div_pos.mpr hq).le
    have hexp : q * (1 / q) = (1 : ℝ) := by field_simp [hq.ne']
    rw [← Real.rpow_mul (apply_nonneg p z), hexp, Real.rpow_one] at h
    exact h
  change p z ≤ 1 - δ
  dsimp [δ]
  linarith only [hroot]

end MarkovSuperreflexivity

end OAI
