import Mathlib
import OAI.Geometry.IntegralFillings.Currents.ComponentMass
import OAI.Geometry.IntegralFillings.Currents.ActionLimits

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace SharpIntegralFillings
namespace BorelCoefficients
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable {k : ℕ} {T : Functional X k} {S : ℕ → Functional X k}
  (μ : ℕ → Measure X) [∀ i, IsFiniteMeasure (μ i)] [IsFiniteMeasure (Measure.sum μ)]
omit [IsFiniteMeasure (Measure.sum μ)] in
lemma summable_borelAction (hS : ∀ i, IsMetricCurrent (S i))
    (hμ : ∀ i, Controls (S i) (μ i))
    {b : X → ℝ} (hb : Integrable b (Measure.sum μ))
    (π : Fin k → X → ℝ) (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) :
    Summable (fun i => borelAction (μ i) (hS i) b π) := by
  choose K hK using hπ
  have hs : Summable (fun i => ∫ x, |b x| ∂μ i) := by
    simpa only [Real.norm_eq_abs,abs_abs] using hb.abs.summable_integral
  apply (hs.mul_left (∏ j, (K j : ℝ))).of_norm_bounded
  intro i
  simpa only [Real.norm_eq_abs] using borelAction_bound (μ i) (hS i) (hμ i)
    (hb.mono_measure (Measure.le_sum μ i)) π K hK

omit [IsFiniteMeasure (Measure.sum μ)] in
lemma borelAction_sum_difference_bound (hS : ∀ i, IsMetricCurrent (S i))
    (hμ : ∀ i, Controls (S i) (μ i))
    {b c : X → ℝ} (hb : Integrable b (Measure.sum μ))
    (hc : Integrable c (Measure.sum μ))
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ j, LipschitzWith (K j) (π j)) :
    |(∑' i, borelAction (μ i) (hS i) b π)-(∑' i, borelAction (μ i) (hS i) c π)| ≤
      (∏ j, (K j : ℝ)) * ∫ x, |b x-c x| ∂Measure.sum μ := by
  have hsb := summable_borelAction μ hS hμ hb π (fun j => ⟨K j,hK j⟩)
  have hsc := summable_borelAction μ hS hμ hc π (fun j => ⟨K j,hK j⟩)
  have hbc : Integrable (fun x => b x-c x) (Measure.sum μ) := hb.sub hc
  have hs : Summable (fun i => ∫ x, |b x-c x| ∂μ i) := by
    simpa only [Real.norm_eq_abs,abs_abs] using hbc.abs.summable_integral
  rw [←hsb.tsum_sub hsc,integral_sum_measure hbc.abs,←tsum_mul_left]
  calc
    |∑' i, (borelAction (μ i) (hS i) b π-borelAction (μ i) (hS i) c π)| ≤
      ∑' i, |borelAction (μ i) (hS i) b π-borelAction (μ i) (hS i) c π| := by
        simpa only [Real.norm_eq_abs] using
          (norm_tsum_le_tsum_norm
            (f := fun i => borelAction (μ i) (hS i) b π-borelAction (μ i) (hS i) c π)
            (hsb.sub hsc).norm)
    _ ≤ ∑' i, (∏ j, (K j : ℝ)) * ∫ x, |b x-c x| ∂μ i :=
      (hsb.sub hsc).abs.tsum_le_tsum
        (fun i => borelAction_difference_bound (μ i) (hS i) (hμ i)
          (hb.mono_measure (Measure.le_sum μ i)) (hc.mono_measure (Measure.le_sum μ i)) π K hK)
        (hs.mul_left _)

lemma borelAction_sum (hT : IsMetricCurrent T) (hS : ∀ i, IsMetricCurrent (S i))
    (hμ : ∀ i, Controls (S i) (μ i))
    (heq : ∀ b π, T b π = ∑' i, S i b π)
    {b : X → ℝ} (hb : Integrable b (Measure.sum μ))
    (π : Fin k → X → ℝ) (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) :
    borelAction (Measure.sum μ) hT b π = ∑' i, borelAction (μ i) (hS i) b π := by
  obtain ⟨f,hf⟩ := exists_lipschitz_approximation (Measure.sum μ) hb
  have hfi (j) := integrable_boundedLip (Measure.sum μ) (f j).property
  have hleft := borelAction_tendsto (Measure.sum μ) hT (controls_sum hμ heq)
    hb hfi hf π hπ
  have hright : Tendsto (fun j => ∑' i, borelAction (μ i) (hS i) (f j).val π) atTop
      (𝓝 (∑' i, borelAction (μ i) (hS i) b π)) := by
    choose K hK using hπ
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun j => borelAction_sum_difference_bound μ hS hμ (hfi j) hb π K hK)
    simpa only [mul_zero] using hf.const_mul (∏ i, (K i : ℝ))
  have hseq : (fun j => borelAction (Measure.sum μ) hT (f j).val π) =
      (fun j => ∑' i, borelAction (μ i) (hS i) (f j).val π) := by
    ext j
    rw [borelAction_eq _ hT (controls_sum hμ heq) ⟨(f j).property,hπ⟩,heq]
    apply tsum_congr
    intro i
    exact (borelAction_eq (μ i) (hS i) (hμ i) ⟨(f j).property,hπ⟩).symm
  rw [hseq] at hleft
  exact tendsto_nhds_unique hleft hright

end BorelCoefficients
end SharpIntegralFillings

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
open BorelCoefficients

end SharpIntegralFillings
end

end OAI
