import OAI.MeasureTheory.Falconer.Estimates.CommonTubeKernel

namespace OAI

/-! Separating the scale power from the truncated common-tube kernel. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem truncatedPlanarDistance_inverse_power_le {δ b : ℝ} (_hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (x y : Space 2) :
    (1/truncatedPlanarDistance δ x y)^b ≤
      1+(1/max (dist x y) δ)^b := by
  rcases le_total (dist x y) 1 with hd | hd
  · simp only [truncatedPlanarDistance,min_eq_right hd,max_comm δ (dist x y)]
    linarith
  · simp only [truncatedPlanarDistance,min_eq_left hd,max_eq_right hδ1,
      div_one,Real.one_rpow]
    have hp : 0 ≤ (1/max (dist x y) δ)^b := by positivity
    linarith

theorem intersect_tube_power_bound {δ b K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hb : 0 ≤ b) (hK : 1 ≤ K) (T U : Finset (Space 2)) (x y : Space 2)
    (hx0 : |x 0| ≤ 1) (hchart : InBoundedLineChart T)
    (hx : ∀ l ∈ T, TubeIncident δ x l) (hy : ∀ l ∈ U, TubeIncident δ y l)
    (hball : NormalizedFiniteBallBound δ b K T) :
    ((T ∩ U).card : ℝ) ≤
      (K*(80*δ)^b*(T.card : ℝ))*(1+(1/max (dist x y) δ)^b) := by
  have hr := (truncatedPlanarDistance_bounds hδ hδ1 x y).1
  have he : (80*δ/truncatedPlanarDistance δ x y)^b =
      (80*δ)^b*(1/truncatedPlanarDistance δ x y)^b := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    ring
  have hh := intersect_tube_kernel_bound hδ hδ1 hb hK T U x y hx0 hchart hx hy hball
  rw [he] at hh
  apply hh.trans
  have hp := mul_le_mul_of_nonneg_left (truncatedPlanarDistance_inverse_power_le hδ hδ1 x y (b := b))
    (show 0 ≤ K*(80*δ)^b*(T.card : ℝ) by positivity)
  convert hp using 1
  ring

end Falconer

end OAI
