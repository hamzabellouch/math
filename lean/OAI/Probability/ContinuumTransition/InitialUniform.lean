import OAI.Probability.ContinuumTransition.KacUniform

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma core_transform_locally_uniform {T a : ℝ} (hT : 1 < T) (ha : 0 < a) (hTa : 1024*a < T) :
    TendstoLocallyUniformlyOn
      (fun n : ℕ => meanField (physicalPressure (coreProfile ((n:ℝ)+T)) ((n:ℝ)+T)) a)
      (threeMeanField packingDensity a) atTop (ball initialPoint (1/2)) := by
  let Q := fun n : ℕ => physicalPressure (coreProfile ((n:ℝ)+T)) ((n:ℝ)+T)
  let P := fun n : ℕ => meanField (Q n) a
  have hQt : TendstoLocallyUniformlyOn Q (threeCore packingDensity) atTop pressureDomain := by
    exact locallyUniform_reindex core_pressure_locally_uniform (tendsto_atTop_add_const_right atTop T tendsto_natCast_atTop_atTop)
  have ht (n : ℕ) : 1 < (n:ℝ)+T := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hat (n : ℕ) : 1024*a < (n:ℝ)+T := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hQ (n : ℕ) : ConvexOn ℝ pressureDomain (Q n) := by
    simpa only [physicalProfile_zero] using physical_convex_bounded (ht n)
      (fun _ : ℕ => le_refl (0:ℝ)) (fun _ : ℕ => le_refl (1:ℝ)) summable_zero (by simpa using (show 0 ≤ (n:ℝ)+T by linarith [ht n]))
  have hP (n : ℕ) : IsMeanField (Q n) a (P n) := by
    simpa only [physicalProfile_zero] using (physical_meanField_bounded (ht n) ha
      (fun _ : ℕ => le_refl (0:ℝ)) (fun _ : ℕ => le_refl (1:ℝ)) summable_zero
      (by simpa using (show 0 ≤ (n:ℝ)+T by linarith [ht n])) (hat n)).1
  apply convex_pointwise_locally_uniform isOpen_ball
  · exact Eventually.of_forall fun n => (meanField_convex (hQ n) (hP n)).subset
      (ball_subset_closedBall.trans (initial_ball_moderate.trans moderateBox_subset)) (convex_ball _ _)
  · intro x hx
    apply meanField_tendsto_of_bounded_maximizers hQt
      ((threeCore_convex packingDensity).continuousOn isOpen_pressureDomain)
      tendsto_const_nhds hP (three_meanField ha.le) (moderateBox_subset (initial_ball_moderate (ball_subset_closedBall hx)))
      tendsto_const_nhds (fun _ => moderateBox_subset (initial_ball_moderate (ball_subset_closedBall hx)))
    intro n
    simpa only [physicalProfile_zero] using physical_meanField_bounded_attainment (ht n) ha
      (fun _ : ℕ => le_refl (0:ℝ)) (fun _ : ℕ => le_refl (1:ℝ)) summable_zero
      (by simpa using (show 0 ≤ (n:ℝ)+T by linarith [ht n])) (hat n)
      (initial_ball_moderate (ball_subset_closedBall hx))

end ContinuumTemperature
end
end

end OAI
