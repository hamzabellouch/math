import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.AffineCalculus
import OAI.Geometry.CAT0Fillings.Calculus.Smoothing

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

lemma LipschitzWith.integral_deriv_eq_sub {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (a b : ℝ) :
    ∫ t in a..b, deriv f t = f b - f a := by
  obtain ⟨g,hg,hpt,hderiv⟩ := exists_smooth_lipschitz_approximation volume hf
  have hbound (j : ℕ) (t : ℝ) : ‖deriv (g j) t‖ ≤ K :=
    norm_deriv_le_of_lipschitz (hg j).2
  have hlim : ∀ᵐ t ∂volume,
      Tendsto (fun j => deriv (g j) t) atTop (𝓝 (deriv f t)) := by
    filter_upwards [hderiv] with t ht
    have H := ((ContinuousLinearMap.apply ℝ ℝ (1:ℝ)).continuous.tendsto
      (fderiv ℝ f t)).comp ht
    exact H
  have hi (j : ℕ) : IntervalIntegrable (deriv (g j)) volume a b :=
    ((hg j).1.continuous_deriv (by norm_num)).intervalIntegrable a b
  have hlimI : Tendsto (fun j => ∫ t in a..b, deriv (g j) t) atTop
      (𝓝 (∫ t in a..b, deriv f t)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (bound := fun _ => (K:ℝ))
    · exact Filter.Eventually.of_forall (fun j => ((hg j).1.continuous_deriv (by norm_num)).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun j => Filter.Eventually.of_forall (fun t _ => hbound j t))
    · exact intervalIntegrable_const
    · exact hlim.mono (fun _ ht _ => ht)
  have heq (j : ℕ) : ∫ t in a..b, deriv (g j) t = g j b - g j a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => ((hg j).1.differentiable (by norm_num) t).hasDerivAt) (hi j)
  simp only [heq] at hlimI
  exact tendsto_nhds_unique hlimI ((hpt b).sub (hpt a))

end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
local notation "BL" => boundedLipSubmodule (X := X)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma lipschitz_slice {f : ℝ × X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (t : ℝ) :
    LipschitzWith K (fun x => f (t,x)) := by
  simpa [Function.comp_def] using hf.comp ((LipschitzWith.const t).prodMk
    (LipschitzWith.id : LipschitzWith 1 (id : X → X)))

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma lipschitz_time {f : ℝ × X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (x : X) :
    LipschitzWith K (fun t => f (t,x)) := by
  simpa [Function.comp_def] using hf.comp ((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).prodMk
    (LipschitzWith.const x))

omit [MeasurableSpace X] [BorelSpace X] in
lemma boundedLip_of_lipschitz_compact {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    BoundedLip f := by
  refine ⟨⟨K,hf⟩,?_⟩
  obtain ⟨b,hb⟩ := (isCompact_range hf.continuous.abs).bddAbove
  exact ⟨b,fun x => hb (mem_range_self x)⟩

omit [CompactSpace X] in
lemma measurable_timeDeriv {f : ℝ × X → ℝ} (hf : Continuous f) :
    Measurable (fun p : ℝ × X => deriv (fun t => f (t,p.2)) p.1) := by
  exact (measurable_deriv_with_param (f := fun x t => f (t,x))
    (hf.comp continuous_swap)).comp measurable_swap

omit [CompactSpace X] in
lemma integrable_timeDeriv {f : ℝ × X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (μ : Measure X) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (fun x => deriv (fun s => f (s,x)) t) μ := by
  apply (integrable_const (K:ℝ)).mono'
    ((measurable_timeDeriv hf.continuous).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  filter_upwards with x
  exact norm_deriv_le_of_lipschitz (lipschitz_time hf x)

lemma ae_time_hasDeriv {f : ℝ × X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (μ : Measure X) [IsFiniteMeasure μ] :
    ∀ᵐ t ∂volume, ∀ᵐ x ∂μ, HasDerivAt (fun s => f (s,x))
      (deriv (fun s => f (s,x)) t) t := by
  have hmeas := measurableSet_of_differentiableAt_with_param ℝ
    (f := fun x t => f (t,x)) (hf.continuous.comp continuous_swap)
  have hp : ∀ᵐ p ∂μ.prod volume, DifferentiableAt ℝ (fun t => f (t,p.1)) p.2 := by
    apply (ae_prod_iff_ae_ae hmeas).mpr
    filter_upwards with x
    exact (lipschitz_time hf x).ae_differentiableAt
  have hq := (Measure.measurePreserving_swap (μ := volume) (ν := μ)).quasiMeasurePreserving.ae hp
  filter_upwards [ae_ae_of_ae_prod hq] with t ht
  filter_upwards [ht] with x hx
  exact hx.hasDerivAt

end CAT0Fillings
end
end

end OAI
