import OAI.Geometry.RCD.Metric.RescaledBallVolume

namespace OAI

/-! # A positive fixed-radius volume bound on every bounded region -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.ball_volume_lower_on_bounded_region {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X) (L r : ℝ) (hr : 0 < r) :
    ∃ m : ℝ, 0 < m ∧ ∀ y, dist y p ≤ L → m ≤ (hausdorff n X).real (ball y r) := by
  let B := max r (L+1)
  have hB : 0 < B := hr.trans_le (le_max_left _ _)
  have hrB : r/B ≤ 1 := (div_le_one hB).mpr (le_max_left _ _)
  have hδ : 0 < r/B := div_pos hr hB
  let a := |K| * B^2
  have ha : 0 ≤ a := mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hcurv : -a ≤ K*B^2 := by
    have hh := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg B)
    simpa only [a,neg_mul] using hh
  let m := ((r/B)/(2*Real.exp (4*Real.sqrt a)))^n*(hausdorff n X).real (ball p B)
  have hV : 0 < (hausdorff n X).real (ball p B) :=
    ENNReal.toReal_pos (hX.fullSupport p B hB).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hm : 0 < m := mul_pos (pow_pos (div_pos hδ (by positivity)) _) hV
  refine ⟨m,hm,?_⟩
  intro y hy
  have hyB : dist y p ≤ B := hy.trans (by dsimp only [B]; linarith [le_max_right r (L+1)])
  have hh := hX.rescaled_ball_volume_lower hn ha hδ hrB p B hB hcurv y hyB
  have he : r/B*B = r := div_mul_cancel₀ _ hB.ne'
  simpa only [he] using hh

end RegularPointCoordinates

end

end OAI
