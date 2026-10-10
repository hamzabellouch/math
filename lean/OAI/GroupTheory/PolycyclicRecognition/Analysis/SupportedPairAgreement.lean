import OAI.GroupTheory.PolycyclicRecognition.Analysis.UniformProfileConcentration

namespace OAI

/-! # Recovering equality of supported endpoint profiles from concentration -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

/-- Endpoint concentration identifies the two profiles in every supported
joint limit. Intermediate chains may use a different compact profile family. -/
theorem supported_pair_eq_of_concentration
    {V W A : Type*} [TopologicalSpace V] [NormedAddCommGroup W] [MeasurableSpace A]
    (S : Set C(V, W)) [MeasurableSpace S] [BorelSpace S]
    [BorelSpace (S × S)] [HasOuterApproxClosed (S × S)]
    (μ : ProbabilityMeasure A) (pair : ℕ → A → S × S) (hp : ∀ n, Measurable (pair n))
    (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map μ (pair n)) atTop (𝓝 ν))
    (Z : Set V) [CompactSpace Z]
    (hconc : ∀ η : ℝ, 0 < η → Tendsto (fun n => (μ : Measure A)
      {a | η ≤ dist ((pair n a).1.val.restrict Z) ((pair n a).2.val.restrict Z)})
      atTop (𝓝 0))
    {f : S × S} (hf : f ∈ (ν : Measure (S × S)).support) :
    ∀ z ∈ Z, f.1.val z = f.2.val z := by
  let err : S × S → ℝ := fun f => dist (f.1.val.restrict Z) (f.2.val.restrict Z)
  have he : Continuous err :=
    ((ContinuousMap.continuous_restrict Z).comp
      (continuous_subtype_val.comp continuous_fst)).dist
    ((ContinuousMap.continuous_restrict Z).comp
      (continuous_subtype_val.comp continuous_snd))
  have hz : err f = 0 := eq_zero_on_support_of_probability_tendsto_zero
    (fun n => ProbabilityMeasure.map μ (pair n)) ν hν err he (fun _ => dist_nonneg)
    (by
      intro η hη
      apply (hconc η hη).congr'
      filter_upwards [] with n
      exact (ProbabilityMeasure.map_apply' μ (hp n).aemeasurable
        (isClosed_le continuous_const he).measurableSet).symm) hf
  have heq : f.1.val.restrict Z = f.2.val.restrict Z := dist_eq_zero.mp hz
  intro z hz
  exact congrArg (fun q : C(Z, W) => q ⟨z, hz⟩) heq

end PolycyclicRecognition

end

end OAI
