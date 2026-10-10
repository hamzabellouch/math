import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselBounds

namespace OAI

/-! Local dominated continuity of the fixed positive Bessel integral. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicBesselHeat_local_bound {a x t : ℝ} (hax : a ≤ x) (ht : 0 < t) :
    ‖cubicBesselHeat x t‖ ≤ t^(-4/3:ℝ)*Real.exp (-a/t) := by
  rw [Real.norm_eq_abs,abs_of_nonneg (cubicBesselHeat_nonneg ht)]
  unfold cubicBesselHeat
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hex : Real.exp (-x/t) ≤ Real.exp (-a/t) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (neg_le_neg hax) ht.le
  calc
    _ ≤ t^(-4/3:ℝ)*1*Real.exp (-a/t) := by gcongr
    _ = _ := by ring

lemma cubicBessel_integral_continuousAt {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun y => ∫ t in Ioi (0:ℝ), cubicBesselHeat y t) x := by
  have hi : IntegrableOn (fun t : ℝ => t^(-4/3:ℝ)*Real.exp (-(x/2)/t)) (Ioi 0) := by
    convert integrable_inverse_laplace_rpow (by norm_num : (0:ℝ) < 1/3)
      (show 0 < x/2 by positivity) using 1; norm_num
  apply continuousAt_of_dominated (bound := fun t : ℝ => t^(-4/3:ℝ)*Real.exp (-(x/2)/t))
  · exact Eventually.of_forall (fun y => by
      apply Measurable.aestronglyMeasurable
      unfold cubicBesselHeat
      fun_prop)
  · filter_upwards [eventually_gt_nhds (show x/2 < x by linarith)] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicBesselHeat_local_bound hy.le ht
  · exact hi
  · filter_upwards with t
    unfold cubicBesselHeat
    fun_prop

/-- The fixed kernel is continuous on its positive domain. -/
theorem cubicBesselKernel_continuousOn : ContinuousOn cubicBesselKernel (Ioi 0) := by
  intro x hx
  exact ((Real.continuousAt_rpow_const x (1/6:ℝ) (Or.inl (ne_of_gt hx))).mul
    (cubicBessel_integral_continuousAt hx)).continuousWithinAt

end CubicFirstMoment

end

end OAI
