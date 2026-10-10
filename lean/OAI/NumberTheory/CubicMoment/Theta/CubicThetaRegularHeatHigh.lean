import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFullGaussianMellin

namespace OAI

/-! The large-time Mellin integral is continuous at the critical exponent,
with domination supplied by the proved height mass at exponent three. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaFullGaussian_nonneg (p : ℂ × ℝ) (t : ℝ) :
    0 ≤ cubicThetaFullGaussian p t := tsum_nonneg (fun _ => (Real.exp_pos _).le)

lemma cubicThetaRegularHeatHigh_bound {p : ℂ × ℝ} {s t : ℝ}
    (hs : s ≤ 3) (ht : 1<t) :
    ‖t^(s-1)*cubicThetaFullGaussian p t‖ ≤ t^(3-1:ℝ)*cubicThetaFullGaussian p t := by
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
    (cubicThetaFullGaussian_nonneg p t))]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)) (cubicThetaFullGaussian_nonneg p t)

lemma cubicThetaRegularHeatHigh_integrable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : s ≤ 3) :
    IntegrableOn (fun t : ℝ => t^(s-1)*cubicThetaFullGaussian p t) (Ioi 1) := by
  have h3 := (cubicThetaFullGaussian_mellin_integrable hp (s:=3) (by norm_num)).mono_set
    (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  have hm : Measurable (fun t : ℝ => t^(s-1)*cubicThetaFullGaussian p t) := by
    have hF := cubicThetaFullGaussian_measurable p
    fun_prop
  apply h3.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact cubicThetaRegularHeatHigh_bound hs ht

theorem cubicThetaRegularHeatHigh_integral_tendsto {p : ℂ × ℝ} (hp : 0<p.2) :
    Tendsto (fun s : ℝ => ∫ t in Ioi (1:ℝ),t^(s-1)*cubicThetaFullGaussian p t)
      (𝓝[>] 2) (𝓝 (∫ t in Ioi (1:ℝ),t^(2-1:ℝ)*cubicThetaFullGaussian p t)) := by
  have h3 := (cubicThetaFullGaussian_mellin_integrable hp (s:=3) (by norm_num)).mono_set
    (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => t^(3-1:ℝ)*cubicThetaFullGaussian p t) ?_ ?_ h3 ?_
  · exact Filter.Eventually.of_forall (fun s => by
      have hF := cubicThetaFullGaussian_measurable p
      apply Measurable.aestronglyMeasurable
      fun_prop)
  · have he : ∀ᶠ s : ℝ in 𝓝[>] 2,s<3 :=
      (show ∀ᶠ s : ℝ in 𝓝 2,s<3 from Iio_mem_nhds (by norm_num : (2:ℝ)<3)).filter_mono nhdsWithin_le_nhds
    filter_upwards [he] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicThetaRegularHeatHigh_bound hs.le ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 1<t at ht
    have hc : ContinuousAt (fun s : ℝ => t^(s-1)) 2 :=
      (Real.continuousAt_const_rpow (by linarith : t≠0)).comp (by fun_prop)
    exact (hc.mul continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds

end CubicFirstMoment

end

end OAI
