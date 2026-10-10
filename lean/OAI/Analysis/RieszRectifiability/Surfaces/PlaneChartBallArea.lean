import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.PlaneDiskHausdorffMeasure

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def planeChartBallAreaConstant (n : ℕ) (K L : ℝ≥0) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞) * (K : ℝ≥0∞) * (L : ℝ≥0∞)) ^ n * planeUnitHausdorffMeasure n

theorem planeChartBallAreaConstant_lt_top (n : ℕ) (K L : ℝ≥0) :
    planeChartBallAreaConstant n K L < ⊤ := by
  exact ENNReal.mul_lt_top (by finiteness) (planeUnitHausdorffMeasure_lt_top n)

theorem plane_chart_ball_hausdorffMeasure_le {n d e : ℕ}
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n)
    (C : Set P) (g : C → Ambient e) (K L : ℝ≥0) (hL : 0 < L)
    (hg : LipschitzWith K g) (hsep : AntilipschitzWith L g)
    (p : Ambient e) (r : ℝ) (hr : 0 < r) :
    (μH[(n : ℝ)] : Measure (Ambient e)) (Set.range g ∩ closedBall p r) ≤
      planeChartBallAreaConstant n K L * (ENNReal.ofReal r) ^ n := by
  classical
  by_cases hempty : Set.range g ∩ closedBall p r = ∅
  · rw [hempty, measure_empty]
    exact zero_le
  obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨a, ha⟩ := hy.1
  let T := g ⁻¹' closedBall p r
  have hdomain : (Subtype.val : C → P) '' T ⊆ closedBall a.val (2 * (L : ℝ) * r) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxball : dist (g x) p ≤ r := hx
    have hyball : dist (g a) p ≤ r := by rw [ha]; exact hy.2
    have ht := dist_triangle_right (g x) (g a) p
    have hpair : dist (g x) (g a) ≤ 2 * r := by linarith
    have h := (hsep.le_mul_dist x a).trans (mul_le_mul_of_nonneg_left hpair L.coe_nonneg)
    change dist x.val a.val ≤ 2 * (L : ℝ) * r
    change dist x.val a.val ≤ (L : ℝ) * (2 * r) at h
    linarith
  have hrad : 0 < 2 * (L : ℝ) * r := by
    have hLreal : 0 < (L : ℝ) := hL
    positivity
  have hdom : (μH[(n : ℝ)] : Measure C) T ≤
      (ENNReal.ofReal (2 * (L : ℝ) * r)) ^ n * planeUnitHausdorffMeasure n := by
    have hiso := (isometry_subtype_coe (s := C)).hausdorffMeasure_image
      (Or.inl (show 0 ≤ (n : ℝ) by positivity)) T
    rw [← hiso]
    exact (measure_mono hdomain).trans_eq (plane_closedBall_hausdorffMeasure P hdim a.val _ hrad)
  have himage : g '' T = Set.range g ∩ closedBall p r := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, rfl⟩, hu⟩
    · rintro ⟨⟨u, rfl⟩, hu⟩
      exact ⟨u, hu, rfl⟩
  have harea := hg.hausdorffMeasure_image_le (show 0 ≤ (n : ℝ) by positivity) T
  rw [himage, ENNReal.rpow_natCast] at harea
  calc
    _ ≤ (K : ℝ≥0∞) ^ n * (μH[(n : ℝ)] : Measure C) T := harea
    _ ≤ (K : ℝ≥0∞) ^ n *
        ((ENNReal.ofReal (2 * (L : ℝ) * r)) ^ n * planeUnitHausdorffMeasure n) :=
      mul_le_mul_right hdom _
    _ = planeChartBallAreaConstant n K L * (ENNReal.ofReal r) ^ n := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (L : ℝ)),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
      unfold planeChartBallAreaConstant
      simp only [mul_pow]
      ring

end

end RieszRectifiability

end OAI
