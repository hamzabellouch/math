import OAI.Geometry.RCD.Metric.ConstantDensitySetMass
import OAI.Geometry.RCD.Transport.ReflectedMidpointDiameter

namespace OAI

/-! # Reflection turns the local midpoint bound into the sharp diameter bound -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem compact_volume_le_diameter_ball_of_midpoint {n : ℕ}
    (μ : Measure (Euclidean n)) {S a c : ℝ} (haS : a < S) (hc : 0 < c)
    (hμ : μ.restrict (ball 0 S) = ENNReal.ofReal c • volume.restrict (ball 0 S))
    {A : Set (Euclidean n)} (hA : IsCompact A) (hAsub : A ⊆ closedBall 0 a)
    (hmid : min (μ.real A) (μ.real (Neg.neg '' A)) ≤
      μ.real (midpointSet A (Neg.neg '' A))) :
    volume.real A ≤ volume.real (closedBall (0 : Euclidean n) (diam A/2)) := by
  have hN : IsCompact (Neg.neg '' A) := hA.image continuous_neg
  have hNsub : Neg.neg '' A ⊆ closedBall 0 a := by
    rintro x ⟨y,hy,rfl⟩
    simpa only [mem_closedBall,dist_zero_right,norm_neg] using hAsub hy
  have hM := isCompact_midpointSet hA hN
  have hMsub : midpointSet A (Neg.neg '' A) ⊆ closedBall 0 a := by
    rintro x ⟨⟨y,z⟩,⟨hy,hz⟩,rfl⟩
    rw [mem_closedBall,dist_zero_right,norm_smul,
      Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    have hy0 : ‖y‖ ≤ a := by simpa only [mem_closedBall,dist_zero_right] using hAsub hy
    have hz0 : ‖z‖ ≤ a := by simpa only [mem_closedBall,dist_zero_right] using hNsub hz
    linarith only [norm_add_le y z,hy0,hz0]
  have hAN := real_eq_mul_volume_of_restrict_eq μ hc.le hμ hA.measurableSet
    (hAsub.trans (closedBall_subset_ball haS))
  have hNN := real_eq_mul_volume_of_restrict_eq μ hc.le hμ hN.measurableSet
    (hNsub.trans (closedBall_subset_ball haS))
  have hMN := real_eq_mul_volume_of_restrict_eq μ hc.le hμ hM.measurableSet
    (hMsub.trans (closedBall_subset_ball haS))
  have hneg : volume.real (Neg.neg '' A) = volume.real A :=
    by simpa only [image_neg_eq_neg,Measure.real] using
        congrArg ENNReal.toReal (Measure.measure_neg volume A)
  rw [hAN,hNN,hMN,hneg,min_self] at hmid
  exact (le_of_mul_le_mul_left hmid hc).trans
    (measureReal_mono (reflected_midpoints_subset_closedBall hA.isBounded)
      (isCompact_closedBall (0 : Euclidean n) (diam A/2)).measure_lt_top.ne)

end RegularPointCoordinates

end

end OAI
