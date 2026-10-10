import OAI.Geometry.RCD.Metric.BoundedIsodiametric

namespace OAI

/-! # The sharp lower normalization bound from the diameter inequality -/

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem volume_le_normalized_hausdorff_of_isodiametric {n : ℕ} (hn : 0 < n)
    (hcompact : ∀ A : Set (Euclidean n), IsCompact A →
      volume.real A ≤ volume.real (closedBall (0 : Euclidean n) (diam A/2))) :
    volume ≤ hausdorff n (Euclidean n) := by
  let C := volume (ball (0 : Euclidean n) 1)/(2:ℝ≥0∞)^n
  have hC0 : C ≠ 0 := (ENNReal.div_pos (measure_ball_pos volume 0 zero_lt_one).ne'
    (by simp)).ne'
  have hCtop : C ≠ ⊤ := ENNReal.div_ne_top measure_ball_ne_top (by positivity)
  have hraw : C⁻¹ • (volume : Measure (Euclidean n)) ≤ Measure.hausdorffMeasure (n:ℝ) := by
    apply Measure.le_hausdorffMeasure _ _ 1 zero_lt_one
    intro A hA
    have hb : Bornology.IsBounded A := isBounded_iff_ediam_ne_top.mpr
      (ne_top_of_le_ne_top (by simp) hA)
    have hh : C⁻¹*volume A ≤ C⁻¹*(C*(ediam A)^n) := by
      gcongr
      exact bounded_volume_le_ediam_pow hn hcompact hb
    change C⁻¹*volume A ≤ ediam A^(n:ℝ)
    rw [← mul_assoc,ENNReal.inv_mul_cancel hC0 hCtop,one_mul] at hh
    simpa only [ENNReal.rpow_natCast] using hh
  intro A
  change volume A ≤ C*Measure.hausdorffMeasure (n:ℝ) A
  calc
    volume A = C*(C⁻¹*volume A) := by
      rw [← mul_assoc,ENNReal.mul_inv_cancel hC0 hCtop,one_mul]
    _ ≤ C*Measure.hausdorffMeasure (n:ℝ) A := by
      gcongr
      exact hraw A

end RegularPointCoordinates

end

end OAI
