import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProfileLawProduct

namespace OAI

/-! # Mean observables of exact measurable profile representatives -/

namespace PolycyclicRecognition

open MeasureTheory

/-- Push a continuous observable through the profile law and use the
actual sample formula, which need only hold almost everywhere. -/
theorem integral_profile_value_map
    {X S W : Type*} [MeasurableSpace X] [MeasurableSpace S]
    [TopologicalSpace S] [BorelSpace S]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [SecondCountableTopology W]
    (μ : ProbabilityMeasure X) (f : X → S) (hf : Measurable f)
    (obs : S → W) (hobs : Continuous obs) (raw : X → W)
    (heq : ∀ᵐ x ∂(μ : Measure X), obs (f x) = raw x) :
    (∫ y, obs y ∂(ProbabilityMeasure.map μ f : Measure S)) =
      ∫ x, raw x ∂(μ : Measure X) := by
  rw [ProbabilityMeasure.toMeasure_map, integral_map hf.aemeasurable hobs.aestronglyMeasurable]
  exact integral_congr_ae heq

/-- Uniform-distance means are unchanged by replacing compact profile
representatives with their original almost-everywhere values. -/
theorem integral_profile_distance_map
    {X S Y : Type*} [MeasurableSpace X] [MeasurableSpace S]
    [TopologicalSpace S] [BorelSpace S] [PseudoMetricSpace Y]
    (μ : ProbabilityMeasure X) (f : X → S) (hf : Measurable f)
    (obs : S → Y) (hobs : Continuous obs) (raw : X → Y)
    (heq : ∀ᵐ x ∂(μ : Measure X), obs (f x) = raw x) (y : Y) :
    (∫ z, dist (obs z) y ∂(ProbabilityMeasure.map μ f : Measure S)) =
      ∫ x, dist (raw x) y ∂(μ : Measure X) := by
  have hd : Continuous (fun z => dist (obs z) y) := hobs.dist continuous_const
  rw [ProbabilityMeasure.toMeasure_map, integral_map hf.aemeasurable hd.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [heq] with x hx
  rw [hx]

end PolycyclicRecognition

end OAI
