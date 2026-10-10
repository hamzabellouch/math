import OAI.Geometry.RCD.Metric.RescaledBallVolume

namespace OAI

/-! # Polynomial lower bounds for kernel normalization balls -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Every small normalization ball with center in twice the working ball
retains a dimensional polynomial fraction of the working volume. -/
theorem NoncollapsedRCD.heat_ball_volume_lower {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X) {R t : ℝ}
    (hR : 0 < R) (hcurv : -1 ≤ K*R^2) (ht : 0 < t) (htR : t ≤ R^2)
    (z : X) (hz : dist z p ≤ 2*R) :
    (Real.sqrt t/(4*Real.exp 8*R))^n*(hausdorff n X).real (ball p R) ≤
      (hausdorff n X).real (ball z (Real.sqrt t)) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsR : Real.sqrt t ≤ R := by nlinarith [Real.sq_sqrt ht.le,Real.sqrt_nonneg t]
  have hd : 0 < Real.sqrt t/(2*R) := by positivity
  have hd1 : Real.sqrt t/(2*R) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hk : -(4:ℝ) ≤ K*(2*R)^2 := by nlinarith only [hcurv]
  have hb := hX.rescaled_ball_volume_lower hn (show (0:ℝ) ≤ 4 by norm_num) hd hd1
    p (2*R) (by positivity) hk z hz
  have hradius : Real.sqrt t/(2*R)*(2*R) = Real.sqrt t := by field_simp
  have hcoef : (Real.sqrt t/(2*R))/(2*Real.exp (4*Real.sqrt 4)) =
      Real.sqrt t/(4*Real.exp 8*R) := by
    norm_num
    ring
  rw [hradius,hcoef] at hb
  have hv : (hausdorff n X).real (ball p R) ≤ (hausdorff n X).real (ball p (2*R)) :=
    measureReal_mono (ball_subset_ball (by linarith)) (hX.finiteOnBounded _ isBounded_ball).ne
  exact (mul_le_mul_of_nonneg_left hv (by positivity)).trans hb

end RegularPointCoordinates

end

end OAI
