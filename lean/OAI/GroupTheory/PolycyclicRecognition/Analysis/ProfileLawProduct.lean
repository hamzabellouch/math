import OAI.GroupTheory.PolycyclicRecognition.Analysis.OccupationSampling

namespace OAI

/-! # Exact product laws of measurable profile maps -/

namespace PolycyclicRecognition

open MeasureTheory Set

/-- Independent pushforward samples have the pushed-forward product law. -/
theorem probability_map_prod_apply
    {X S : Type*} [MeasurableSpace X] [MeasurableSpace S]
    (μ : ProbabilityMeasure X) (f : X → S) (hf : Measurable f)
    (B : Set (S × S)) (hB : MeasurableSet B) :
    (ProbabilityMeasure.map μ f : Measure S).prod
      (ProbabilityMeasure.map μ f : Measure S) B =
      (μ : Measure X).prod (μ : Measure X) ((Prod.map f f) ⁻¹' B) := by
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_prod_map (μ : Measure X) (μ : Measure X) hf hf,
    Measure.map_apply (hf.prodMap hf) hB]

/-- Representatives agreeing almost everywhere induce exactly the same
pairwise distance probabilities. -/
theorem probability_map_pair_distance_of_ae_eq
    {X S Y : Type*} [MeasurableSpace X] [MeasurableSpace S]
    [PseudoMetricSpace Y]
    (μ : ProbabilityMeasure X) (f : X → S) (hf : Measurable f)
    (F : S → Y) (raw : X → Y) (heq : ∀ᵐ x ∂(μ : Measure X), F (f x) = raw x)
    (η : ℝ) (hB : MeasurableSet {p : S × S | η ≤ dist (F p.1) (F p.2)}) :
    (ProbabilityMeasure.map μ f : Measure S).prod
      (ProbabilityMeasure.map μ f : Measure S) {p | η ≤ dist (F p.1) (F p.2)} =
      (μ : Measure X).prod (μ : Measure X) {p | η ≤ dist (raw p.1) (raw p.2)} := by
  rw [probability_map_prod_apply μ f hf _ hB]
  apply measure_congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp heq,
    Measure.quasiMeasurePreserving_snd.ae_eq_comp heq] with p hp hq
  simp only [Function.comp_apply] at hp hq
  apply propext
  change (η ≤ dist (F (f p.1)) (F (f p.2))) ↔ η ≤ dist (raw p.1) (raw p.2)
  rw [hp, hq]

end PolycyclicRecognition

end OAI
