import Mathlib.Analysis.SpecificLimits.Normed
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDyadicShells
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityKernelPacking

namespace OAI

/-! # Summable cubic weights on the dyadic height shells -/

namespace Ostmann

open Set

noncomputable def densityHeightWeight (T x : ℝ) : ℝ := densityCubicWeight (x / T)

 theorem densityHeightWeight_nonneg (T x : ℝ) : 0 ≤ densityHeightWeight T x :=
  densityCubicWeight_nonneg _

 theorem densityHeightWeight_continuous (T : ℝ) : Continuous (densityHeightWeight T) := by
  unfold densityHeightWeight densityCubicWeight
  exact continuous_const.div
    ((continuous_const.add (continuous_id.div_const T).abs).pow 3) (fun x => by positivity)

 theorem densityHeightWeight_shell (T : ℝ) (hT : 0 < T) (j : ℕ) (x : ℝ)
    (hx : x ∈ densityHeightShell T (j + 1)) :
    densityHeightWeight T x ≤ (1 / 8 : ℝ) ^ j := by
  have ha : (2 : ℝ) ^ j * T < |x| := by
    have h := hx.2
    rw [densityHeightBall_mem] at h
    exact lt_of_not_ge h
  have hd : (2 : ℝ) ^ j ≤ 1 + |x / T| := by
    rw [abs_div, abs_of_pos hT]
    have hh : (2 : ℝ) ^ j < |x| / T := (lt_div_iff₀ hT).mpr ha
    linarith
  calc
    densityHeightWeight T x ≤ 1 / ((2 : ℝ) ^ j) ^ 3 := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ (by positivity) hd 3
    _ = (1 / 8 : ℝ) ^ j := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, one_div_pow]
      norm_num

 theorem density_height_energy_summable (k : ℕ) :
    Summable (fun j : ℕ => (j + 2 : ℝ) ^ k * (1 / 4 : ℝ) ^ j) := by
  have h0 : Summable (fun j : ℕ => (j : ℝ) ^ k * (1 / 4 : ℝ) ^ j) :=
    summable_pow_mul_geometric_of_norm_lt_one k (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  have h : Summable (fun j : ℕ => ((j + 2 : ℕ) : ℝ) ^ k * (1 / 4 : ℝ) ^ (j + 2)) :=
    (summable_nat_add_iff 2).mpr h0
  have hm := h.mul_right (16 : ℝ)
  convert hm using 1
  funext j
  push_cast
  rw [pow_add]
  ring

noncomputable def densityHeightEnergyConstant (k : ℕ) : ℝ :=
  1 + 2 * ∑' j : ℕ, (j + 2 : ℝ) ^ k * (1 / 4 : ℝ) ^ j

 theorem densityHeightEnergyConstant_pos (k : ℕ) : 0 < densityHeightEnergyConstant k := by
  have hh : 0 ≤ ∑' j : ℕ, (j + 2 : ℝ) ^ k * (1 / 4 : ℝ) ^ j := tsum_nonneg (fun _ => by positivity)
  unfold densityHeightEnergyConstant
  linarith

end Ostmann

end OAI
