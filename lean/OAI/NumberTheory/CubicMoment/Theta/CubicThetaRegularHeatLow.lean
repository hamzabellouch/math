import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFullGaussianRemainder
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFullGaussianMellin

namespace OAI

/-! The small-time Mellin remainder is integrable and continuous at the
critical exponent after subtracting the proved heat coefficient. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace CubicFirstMoment

def cubicThetaRegularHeatLow (p : ℂ × ℝ) (s t : ℝ) : ℝ :=
  t^(s-1)*(cubicThetaFullGaussian p t-(4*Real.pi^2/243)/t^2)

lemma cubicThetaRegularHeatLow_measurable (p : ℂ × ℝ) (s : ℝ) :
    Measurable (cubicThetaRegularHeatLow p s) := by
  have hF := cubicThetaFullGaussian_measurable p
  unfold cubicThetaRegularHeatLow
  fun_prop

lemma cubicThetaRegularHeatLow_bound {p : ℂ × ℝ} {M s t : ℝ}
    (hM : 0 ≤ M) (hbound : |cubicThetaFullGaussian p t-(4*Real.pi^2/243)/t^2| ≤ M)
    (hs : 2 ≤ s) (ht : t ∈ Ioc (0:ℝ) 1) :
    ‖cubicThetaRegularHeatLow p s t‖ ≤ M*t := by
  have hp : t^(s-1) ≤ t := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2
      (show (1:ℝ) ≤ s-1 by linarith)
  rw [cubicThetaRegularHeatLow,Real.norm_eq_abs,abs_mul,
    abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
  exact (mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg ht.1.le _)).trans
    (by nlinarith)

lemma cubicThetaRegularHeatLow_integrable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2 ≤ s) : IntegrableOn (cubicThetaRegularHeatLow p s) (Ioc 0 1) := by
  obtain ⟨M,hM,hbound⟩ := cubicThetaFullGaussian_bounded_remainder hp
  have hi : IntegrableOn (fun t : ℝ => M*t) (Ioc 0 1) :=
    ((continuous_const.mul continuous_id).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  apply hi.mono' (cubicThetaRegularHeatLow_measurable p s).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact cubicThetaRegularHeatLow_bound hM (hbound t ht.1 ht.2) hs ht

theorem cubicThetaRegularHeatLow_integral_tendsto {p : ℂ × ℝ} (hp : 0<p.2) :
    Tendsto (fun s : ℝ => ∫ t in Ioc (0:ℝ) 1,cubicThetaRegularHeatLow p s t)
      (𝓝[>] 2) (𝓝 (∫ t in Ioc (0:ℝ) 1,cubicThetaRegularHeatLow p 2 t)) := by
  obtain ⟨M,hM,hbound⟩ := cubicThetaFullGaussian_bounded_remainder hp
  have hi : IntegrableOn (fun t : ℝ => M*t) (Ioc 0 1) :=
    ((continuous_const.mul continuous_id).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  apply tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => M*t) ?_ ?_ hi ?_
  · exact Filter.Eventually.of_forall (fun s => (cubicThetaRegularHeatLow_measurable p s).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact cubicThetaRegularHeatLow_bound hM (hbound t ht.1 ht.2) hs.le ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hc : ContinuousAt (fun s : ℝ => t^(s-1)) 2 :=
      (Real.continuousAt_const_rpow ht.1.ne').comp (by fun_prop)
    exact (hc.mul continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds

end CubicFirstMoment

end

end OAI
