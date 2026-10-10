import OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor
import OAI.NumberTheory.PiExponent.Polynomials.SimplexLog

namespace OAI

open Filter Topology

namespace PiExponent

noncomputable def translationTermCount (m : ℕ) (v H : ℝ) : ℕ :=
  (⌊H⌋₊ + 1) ^ (2 * m) * (⌊H / v⌋₊ + 1)

theorem tendsto_natFloor_mul_add_one_div {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H : ℝ => ((⌊a * H⌋₊ + 1 : ℕ) : ℝ) / H) atTop (𝓝 a) := by
  have h := (tendsto_natFloor_affine_div ha 0).add (tendsto_id.const_div_atTop (1 : ℝ))
  simpa only [add_zero, id_eq, Nat.cast_add, Nat.cast_one, add_div] using h

theorem tendsto_translationTermCount_normalized (m : ℕ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun H : ℝ => (translationTermCount m v H : ℝ) / H ^ (2 * m + 1))
      atTop (𝓝 (1 / v)) := by
  have h₁ : Tendsto (fun H : ℝ => ((⌊H⌋₊ + 1 : ℕ) : ℝ) / H) atTop (𝓝 1) := by
    simpa only [one_mul] using tendsto_natFloor_mul_add_one_div (show (0 : ℝ) < 1 by norm_num)
  have h₂ : Tendsto (fun H : ℝ => ((⌊H / v⌋₊ + 1 : ℕ) : ℝ) / H)
      atTop (𝓝 (1 / v)) := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using
      tendsto_natFloor_mul_add_one_div (div_pos zero_lt_one hv)
  have h := (h₁.pow (2 * m)).mul h₂
  simp only [one_pow, one_mul] at h
  convert h using 1
  ext H
  simp only [translationTermCount, Nat.cast_mul, Nat.cast_pow, div_pow, div_mul_div_comm,
    pow_succ]

theorem tendsto_log_translationTermCount_div (m : ℕ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun H : ℝ => Real.log (translationTermCount m v H : ℝ) / H)
      atTop (𝓝 0) :=
  tendsto_log_div_of_normalized_pow (tendsto_translationTermCount_normalized m hv)
    (div_pos zero_lt_one hv)

theorem tendsto_log_translationTermCount_div_nat (m : ℕ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun H : ℕ => Real.log (translationTermCount m v (H : ℝ) : ℝ) / (H : ℝ))
      atTop (𝓝 0) :=
  (tendsto_log_translationTermCount_div m hv).comp tendsto_natCast_atTop_atTop

end PiExponent

end OAI
