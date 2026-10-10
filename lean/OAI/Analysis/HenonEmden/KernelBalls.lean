import OAI.Analysis.HenonEmden.OriginCutoff

namespace OAI

universe uE

section KernelBalls

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.WeakPDE
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma shifted_ball_indicator (a r : ℝ) (x y : E) :
    (ball x r).indicator (fun y => ‖x-y‖^a) y =
      (ball (0:E) r).indicator (fun z => ‖z‖^a) (x-y) := by
  by_cases hy : y ∈ ball x r
  · rw [indicator_of_mem hy,indicator_of_mem]
    simpa only [mem_ball,dist_zero_right,dist_eq_norm,sub_zero,norm_sub_rev x y] using hy
  · rw [indicator_of_notMem hy,indicator_of_notMem]
    simpa only [mem_ball,dist_zero_right,dist_eq_norm,sub_zero,norm_sub_rev x y] using hy

lemma integrable_shifted_power_ball (hn : 1 ≤ Module.finrank ℝ E) {a : ℝ}
    (ha : -(Module.finrank ℝ E:ℝ) < a) (r : ℝ) (x : E) :
    Integrable ((ball x r).indicator (fun y => ‖x-y‖^a)) := by
  have hi : IntegrableOn (fun z : E => ‖z‖^a) (ball 0 r) :=
    ((locallyIntegrable_norm_power hn a ha).integrableOn_isCompact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  have hI := hi.integrable_indicator measurableSet_ball
  simpa only [Function.comp_def,← shifted_ball_indicator] using
    (Measure.measurePreserving_sub_left volume x).integrable_comp hI.aestronglyMeasurable |>.mpr hI

lemma integral_shifted_power_ball (a : ℝ) {r : ℝ} (hr : 0 < r) (x : E) :
    (∫ y, (ball x r).indicator (fun y => ‖x-y‖^a) y) =
      r^((Module.finrank ℝ E:ℝ)+a)*(∫ z in ball (0:E) 1, ‖z‖^a) := by
  simp_rw [shifted_ball_indicator]
  rw [integral_sub_left_eq_self (fun z => (ball (0:E) r).indicator (fun z => ‖z‖^a) z) volume x,
    integral_indicator measurableSet_ball,integral_weight_ball_scaling a hr]

lemma rpow_half_double_bound {r s : ℝ} (hr : 0 < r) (hs : r/2 ≤ s) (hs' : s ≤ 2*r) (A : ℝ) :
    s^A ≤ (2:ℝ)^|A| * r^A := by
  have hs0 : 0 < s := by linarith
  by_cases hA : 0 ≤ A
  · calc
      _ ≤ (2*r)^A := Real.rpow_le_rpow hs0.le hs' hA
      _ = _ := by rw [Real.mul_rpow (by norm_num) hr.le,abs_of_nonneg hA]
  · have hA' : A ≤ 0 := (not_le.mp hA).le
    calc
      _ ≤ (r/2)^A := Real.rpow_le_rpow_of_nonpos (by positivity) hs hA'
      _ = _ := by
        rw [Real.div_rpow hr.le (by norm_num),abs_of_nonpos hA',Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_eq_mul_inv,mul_comm]

end HenonLaneEmden.WeakPDE
end
end KernelBalls

end OAI
