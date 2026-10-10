import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

def finiteChartPackingFactor (N : ℕ) : ℝ≥0 := 4 * ((N : ℝ≥0) + 1)

def finiteChartParameterCenter {n : ℕ} (e : Ambient n) (r : ℝ) (N : ℕ) (i : Fin N) : Ambient n :=
  (((i.val : ℝ) + 1) * (r / (2 * ((N : ℝ) + 1)))) • e

theorem finite_chart_parameter_center_mem {n : ℕ}
    (e : Ambient n) (he : ‖e‖ = 1) (r : ℝ) (hr : 0 < r) (N : ℕ) (i : Fin N) :
    finiteChartParameterCenter e r N i ∈ closedBall (0 : Ambient n) (r / 2) := by
  have hi : (i.val : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [mem_closedBall_zero_iff, finiteChartParameterCenter, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), he, mul_one]
  have hden : 0 < 2 * ((N : ℝ) + 1) := by positivity
  rw [← mul_div_assoc, div_le_iff₀ hden]
  nlinarith

theorem finite_chart_parameter_centers_separated {n : ℕ}
    (e : Ambient n) (he : ‖e‖ = 1) (r : ℝ) (hr : 0 < r) (N : ℕ)
    (i j : Fin N) (hij : i ≠ j) :
    r + r ≤ (finiteChartPackingFactor N : ℝ) *
      dist (finiteChartParameterCenter e r N i) (finiteChartParameterCenter e r N j) := by
  let δ := r / (2 * ((N : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hneq : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have habs : 1 ≤ |(i.val : ℝ) - (j.val : ℝ)| := by
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · have h : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have h : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hdist : δ ≤ dist (finiteChartParameterCenter e r N i) (finiteChartParameterCenter e r N j) := by
    rw [dist_eq_norm, finiteChartParameterCenter, finiteChartParameterCenter,
      ← sub_smul, norm_smul, Real.norm_eq_abs, he, mul_one]
    change δ ≤ |((i.val : ℝ) + 1) * δ - ((j.val : ℝ) + 1) * δ|
    rw [show ((i.val : ℝ) + 1) * δ - ((j.val : ℝ) + 1) * δ =
      ((i.val : ℝ) - (j.val : ℝ)) * δ by ring, abs_mul, abs_of_pos hδ]
    simpa only [one_mul] using! mul_le_mul_of_nonneg_right habs hδ.le
  have hid : (finiteChartPackingFactor N : ℝ) * δ = r + r := by
    change (4 * ((N : ℝ) + 1)) * (r / (2 * ((N : ℝ) + 1))) = r + r
    have hN : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [← hid]
  exact mul_le_mul_of_nonneg_left hdist (finiteChartPackingFactor N).coe_nonneg

theorem finite_chart_parameter_island_subset {n : ℕ}
    (e : Ambient n) (he : ‖e‖ = 1) (r : ℝ) (hr : 0 < r) (N : ℕ) (i : Fin N) :
    ball (finiteChartParameterCenter e r N i) (r / (4 * (finiteChartPackingFactor N : ℝ))) ⊆
      ball (0 : Ambient n) r := by
  intro u hu
  have hc : dist (finiteChartParameterCenter e r N i) (0 : Ambient n) ≤ r / 2 :=
    finite_chart_parameter_center_mem e he r hr N i
  have hA : 4 ≤ (finiteChartPackingFactor N : ℝ) := by
    change 4 ≤ 4 * ((N : ℝ) + 1)
    have hN := Nat.cast_nonneg (α := ℝ) N
    linarith
  have hden : 0 < 4 * (finiteChartPackingFactor N : ℝ) := by linarith
  have hrad : r / (4 * (finiteChartPackingFactor N : ℝ)) ≤ r / 4 :=
    (div_le_iff₀ hden).mpr (by nlinarith)
  have ht := dist_triangle u (finiteChartParameterCenter e r N i) (0 : Ambient n)
  have hu' : dist u (finiteChartParameterCenter e r N i) <
      r / (4 * (finiteChartPackingFactor N : ℝ)) := hu
  change dist u (0 : Ambient n) < r
  linarith

end

end RieszRectifiability

end OAI
