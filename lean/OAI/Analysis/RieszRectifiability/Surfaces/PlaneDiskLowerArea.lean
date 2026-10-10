import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.PlaneDiskHausdorffMeasure

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem planeUnitHausdorffMeasure_pos (n : ℕ) :
    0 < planeUnitHausdorffMeasure n := by
  have h := measure_closedBall_pos
    (μH[(Module.finrank ℝ (Ambient n) : ℝ)] : Measure (Ambient n))
    (0 : Ambient n) (by norm_num : (0 : ℝ) < 1)
  simpa only [finrank_euclideanSpace_fin, planeUnitHausdorffMeasure] using! h

def planeDiskLowerAreaConstant (n : ℕ) (L : ℝ≥0) : ℝ≥0∞ :=
  planeUnitHausdorffMeasure n / (L : ℝ≥0∞) ^ n

theorem planeDiskLowerAreaConstant_pos (n : ℕ) (L : ℝ≥0) :
    0 < planeDiskLowerAreaConstant n L := by
  exact ENNReal.div_pos (planeUnitHausdorffMeasure_pos n).ne' (by finiteness)

theorem planeDiskLowerAreaConstant_lt_top (n : ℕ) (L : ℝ≥0) (hL : 0 < L) :
    planeDiskLowerAreaConstant n L < ⊤ := by
  have hL0 : (L : ℝ≥0∞) ≠ 0 := by exact_mod_cast hL.ne'
  exact ENNReal.div_lt_top (planeUnitHausdorffMeasure_lt_top n).ne
    (pow_ne_zero n hL0)

theorem plane_disk_antilipschitz_range_hausdorffMeasure_ge {n d e : ℕ}
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n)
    (a : P) (r : ℝ) (hr : 0 < r) (L : ℝ≥0) (hL : 0 < L)
    (g : closedBall a r → Ambient e) (hg : AntilipschitzWith L g) :
    planeDiskLowerAreaConstant n L * (ENNReal.ofReal r) ^ n ≤
      (μH[(n : ℝ)] : Measure (Ambient e)) (Set.range g) := by
  have h := hg.le_hausdorffMeasure_image (show 0 ≤ (n : ℝ) by positivity) Set.univ
  simp only [Set.image_univ, ENNReal.rpow_natCast,
    plane_closedBall_subtype_hausdorffMeasure P hdim a r hr] at h
  have hL0 : (L : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero n (by exact_mod_cast hL.ne')
  have hLt : (L : ℝ≥0∞) ^ n ≠ ⊤ := by finiteness
  have hdiv := (ENNReal.div_le_iff' hL0 hLt).mpr h
  convert! hdiv using 1
  unfold planeDiskLowerAreaConstant
  simp only [div_eq_mul_inv]
  ring

end

end RieszRectifiability

end OAI
