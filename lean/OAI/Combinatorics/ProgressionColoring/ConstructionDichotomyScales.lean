import OAI.Combinatorics.ProgressionColoring.ConstructionModelBounds
import OAI.Combinatorics.ProgressionColoring.Asymptotics
import OAI.Combinatorics.ProgressionColoring.ConstructionDichotomyDenominator

namespace OAI

/-!
# Actual scale consequences for the geometric dichotomy

These bounds use the numerical `GeometryScales` inequalities and the literal
construction mesh. No geometric conclusion is supplied as a hypothesis.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

variable {k : ℕ}

theorem geometry_dimension_ge_three (g : GeometryScales k) : 3 ≤ dimension k := by
  by_contra h
  have hd : dimension k ≤ 2 := by omega
  have hd' : (dimension k : ℝ) ≤ 2 := by exact_mod_cast hd
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (dimension k)) hd' 2
  have hg := g.local_event_size
  norm_num at hs
  nlinarith

theorem geometry_cutoff_pos (hk : 3 ≤ k) : 0 < cutoff k :=
  cutoff_pos (by omega)

theorem geometry_two_cutoff_le_length (g : GeometryScales k) : 2 * cutoff k ≤ k := by
  exact_mod_cast g.two_cutoff_le_length

/-- The rational-return velocity is no larger than the second mesh width. -/
theorem velocity_le_mesh (s : Data k) (hk : 3 ≤ k) (g : GeometryScales k)
    {v : ℝ} (hv : |v| ≤ 4 * cutoff k * (mesh s hk).H / k) :
    |v| ≤ (mesh s hk).H := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hH : 0 ≤ (mesh s hk).H := by
    rw [mesh_H]
    exact (meshScale_pos (show 0 < k by omega)).le
  have hm : 4 * (cutoff k : ℝ) ≤ k := by
    have := g.heavy_return
    linarith
  apply hv.trans
  apply (div_le_iff₀ hk0).2
  have hmul := mul_le_mul_of_nonneg_right hm hH
  nlinarith

/-- The same velocity lies strictly inside the actual cut-off scale. -/
theorem velocity_lt_cut (s : Data k) (hk : 3 ≤ k) (g : GeometryScales k)
    {v : ℝ} (hv : |v| ≤ 4 * cutoff k * (mesh s hk).H / k) :
    |v| < cutScale k := by
  rw [mesh_H] at hv
  exact hv.trans_lt g.cut_error

/-- The total drift over the progression is less than half a unit. -/
theorem velocity_div_small (s : Data k) (hk : 3 ≤ k) (g : GeometryScales k)
    {h : ℕ} (hh : 0 < h) {v : ℝ}
    (hv : |v| ≤ 4 * cutoff k * (mesh s hk).H / k) :
    (k : ℝ) * |v / (h : ℝ)| < 1 / 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  have hd : |v / (h : ℝ)| ≤ |v| := by
    rw [abs_div, abs_of_pos hh0]
    exact div_le_self (abs_nonneg v) hh1
  have hb : (k : ℝ) * |v| ≤ 4 * cutoff k * (mesh s hk).H := by
    have := (le_div_iff₀ hk0).mp hv
    nlinarith
  have hs : 4 * (cutoff k : ℝ) * (mesh s hk).H < 1 / 2 := by
    simpa only [mesh_H] using g.rational_separation
  exact (mul_le_mul_of_nonneg_left hd hk0.le).trans_lt (hb.trans_lt hs)

/-- The error in the lattice lifting argument remains below one integer. -/
theorem lattice_error_small (s : Data k) (hk : 3 ≤ k) (g : GeometryScales k)
    {h : ℕ} (hh : 0 < h) :
    2 * (mesh s hk).H + 4 * cutoff k * (mesh s hk).H / (h : ℝ) < 1 := by
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  have hH : 0 ≤ (mesh s hk).H := by
    rw [mesh_H]
    exact (meshScale_pos (show 0 < k by omega)).le
  have hn : 0 ≤ 4 * (cutoff k : ℝ) * (mesh s hk).H := by positivity
  have hd := div_le_self hn hh1
  have hs : 2 * (mesh s hk).H + 4 * cutoff k * (mesh s hk).H < 1 := by
    simpa only [mesh_H] using g.lattice_separation
  linarith

/-- Distinct rational returns cannot hide inside one first-system cell. -/
theorem twice_period_uniformWidth_lt_one (s : Data k) (hk : 3 ≤ k)
    (g : GeometryScales k) {h : ℕ} (hmax : h ≤ 2 * cutoff k) :
    2 * (h : ℝ) * (1 / (uniformCount k : ℝ)) < 1 := by
  have hH : 0 ≤ (mesh s hk).H := by
    rw [mesh_H]
    exact (meshScale_pos (show 0 < k by omega)).le
  have hm : (h : ℝ) ≤ 2 * cutoff k := by exact_mod_cast hmax
  have hw := mul_le_mul_of_nonneg_left (uniformWidth_le_meshH s hk)
    (show 0 ≤ 2 * (h : ℝ) by positivity)
  have hp := mul_le_mul_of_nonneg_right hm hH
  have hs : 4 * (cutoff k : ℝ) * (mesh s hk).H < 1 / 2 := by
    simpa only [mesh_H] using g.rational_separation
  nlinarith

end QuantitativeVanDerWaerden.ConstructionModel

end

end OAI
