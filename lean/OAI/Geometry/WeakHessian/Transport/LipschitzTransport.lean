import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.CostMetric

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile59
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma lipschitz_integral_sub_le_cost (μ ν : ProbabilityMeasure X) (o : X)
    (hμ : Integrable (fun x => dist x o^2) (μ:Measure X))
    (hν : Integrable (fun x => dist x o^2) (ν:Measure X))
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) {B : ℝ} (hB : ∀ x,|f x| ≤ B) :
    |(∫ x,f x ∂(μ:Measure X))-(∫ x,f x ∂(ν:Measure X))| ≤
      (L:ℝ)*Real.sqrt (quadraticWassersteinSq (μ:Measure X) (ν:Measure X)) := by
  obtain ⟨q,hqp,hq,hqt⟩ := exists_optimal_coupling_of_moments μ ν o hμ hν
  let : IsProbabilityMeasure q := hqp
  have hfq : Integrable (fun p : X×X => f p.1) q := Integrable.of_bound
    (hf.continuous.comp continuous_fst).aestronglyMeasurable B (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hB p.1)
  have hgq : Integrable (fun p : X×X => f p.2) q := Integrable.of_bound
    (hf.continuous.comp continuous_snd).aestronglyMeasurable B (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hB p.2)
  have hd : MemLp (fun p : X×X => dist p.1 p.2) 2 q :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (integrable_squared_distance_of_cost hqt)
  have hI : (∫ p : X×X,dist p.1 p.2 ∂q) ≤ Real.sqrt (∫ p : X×X,dist p.1 p.2^2 ∂q) := by
    simpa using
      integral_mul_le_sqrt_integral_sq hd (memLp_const (1:ℝ))
  have hF : |(∫ p : X×X,f p.1-f p.2 ∂q)| ≤ (L:ℝ)*(∫ p : X×X,dist p.1 p.2 ∂q) := by
    apply abs_integral_le_integral_abs.trans
    rw [← integral_const_mul]
    apply integral_mono_ae (hfq.sub hgq).abs ((hd.integrable (by norm_num)).const_mul (L:ℝ))
    exact ae_of_all _ fun p => by simpa only [Real.dist_eq,Pi.sub_apply] using hf.dist_le_mul p.1 p.2
  rw [integral_sub hfq hgq,← integral_map measurable_fst.aemeasurable hf.continuous.aestronglyMeasurable,
    ← integral_map measurable_snd.aemeasurable hf.continuous.aestronglyMeasurable,hq.1.1,hq.1.2] at hF
  have he : quadraticWassersteinSq (μ:Measure X) (ν:Measure X) = ∫ p : X×X,dist p.1 p.2^2 ∂q := by
    rw [hq.quadraticWassersteinSq_eq,quadraticTransportCost_eq_integral hqt,ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  rw [he]
  exact hF.trans (mul_le_mul_of_nonneg_left hI L.coe_nonneg)
end WeakHessian

end
end InlinedFile59

end OAI
