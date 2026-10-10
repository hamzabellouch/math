import Mathlib
import OAI.Geometry.IntegralFillings.Currents.BorelAction

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
attribute [local instance] Classical.propDecidable
namespace BorelCoefficients
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
variable {k : ℕ} {T : Functional X k}
lemma borelAction_sub (hT : IsMetricCurrent T) {b c : X → ℝ}
    (hb : Integrable b μ) (hc : Integrable c μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction μ hT (fun x => b x-c x) π =
      borelAction μ hT b π-borelAction μ hT c π := by
  have he : (fun x => b x-c x) = b+(-1 : ℝ) • c := by ext x; simp [sub_eq_add_neg]
  rw [he,borelAction_add μ hT hb (hc.smul (-1)) π hπ,
    borelAction_smul μ hT hc π (-1) hπ]
  ring

lemma borelAction_difference_bound (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b c : X → ℝ} (hb : Integrable b μ) (hc : Integrable c μ)
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ i, LipschitzWith (K i) (π i)) :
    |borelAction μ hT b π-borelAction μ hT c π| ≤
      (∏ i, (K i : ℝ)) * ∫ x, |b x-c x| ∂μ := by
  rw [←borelAction_sub μ hT hb hc π (fun i => ⟨K i,hK i⟩)]
  exact borelAction_bound μ hT hμ (hb.sub hc) π K hK

lemma borelAction_tendsto (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b : X → ℝ} {f : ℕ → X → ℝ} (hb : Integrable b μ)
    (hf : ∀ j, Integrable (f j) μ)
    (hlim : Tendsto (fun j => ∫ x, |f j x-b x| ∂μ) atTop (𝓝 0))
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    Tendsto (fun j => borelAction μ hT (f j) π) atTop (𝓝 (borelAction μ hT b π)) := by
  choose K hK using hπ
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun j => (borelAction_difference_bound μ hT hμ (hf j) hb π K hK))
  simpa only [mul_zero] using hlim.const_mul (∏ i, (K i : ℝ))

lemma borelAction_independent (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {ν : Measure X} [IsFiniteMeasure ν] (hν : Controls T ν)
    {b : X → ℝ} (hbμ : Integrable b μ) (hbν : Integrable b ν)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction μ hT b π = borelAction ν hT b π := by
  obtain ⟨f,hf⟩ := exists_lipschitz_approximation (μ+ν) (hbμ.add_measure hbν)
  have hi (j) := integrable_boundedLip (μ+ν) (f j).property
  have hlμ : Tendsto (fun j => ∫ x, |(f j).val x-b x| ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _)
      (fun j => integral_mono_measure (Measure.le_add_right le_rfl)
        (Eventually.of_forall fun _ => abs_nonneg _) ((hi j).sub (hbμ.add_measure hbν)).abs) hf
  have hlν : Tendsto (fun j => ∫ x, |(f j).val x-b x| ∂ν) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _)
      (fun j => integral_mono_measure (Measure.le_add_left le_rfl)
        (Eventually.of_forall fun _ => abs_nonneg _) ((hi j).sub (hbμ.add_measure hbν)).abs) hf
  have hμlim := borelAction_tendsto μ hT hμ hbμ
    (fun j => integrable_boundedLip μ (f j).property) hlμ π hπ
  have hνlim := borelAction_tendsto ν hT hν hbν
    (fun j => integrable_boundedLip ν (f j).property) hlν π hπ
  simp only [borelAction_eq μ hT hμ ⟨(f _).property,hπ⟩] at hμlim
  simp only [borelAction_eq ν hT hν ⟨(f _).property,hπ⟩] at hνlim
  exact tendsto_nhds_unique hμlim hνlim

end BorelCoefficients
end SharpIntegralFillings

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
end SharpIntegralFillings
end

end OAI
