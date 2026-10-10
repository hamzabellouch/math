import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportedProbabilityRestriction
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactProbabilityProduct

namespace OAI

/-! # Compactly supported starting densities in the profile argument -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

theorem productOccupationLaw_map_right
    {A D E X : Type*} [MeasurableSpace A] [MeasurableSpace D]
    [MeasurableSpace E] [MeasurableSpace X]
    (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure D)
    (f : D → E) (hf : Measurable f) (p : A × E → X) (hp : Measurable p) :
    productOccupationLaw μ (ProbabilityMeasure.map ν f) p =
      productOccupationLaw μ ν (fun z => p (z.1, f z.2)) := by
  apply Subtype.ext
  have hprod : (μ : Measure A).prod (Measure.map f (ν : Measure D)) =
      Measure.map (Prod.map id f) ((μ : Measure A).prod (ν : Measure D)) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map (μ : Measure A) (ν : Measure D) measurable_id hf)
  change Measure.map p ((μ : Measure A).prod (Measure.map f (ν : Measure D))) = _
  rw [hprod, Measure.map_map hp (measurable_id.prodMap hf)]
  rfl

/-- Restricting the starting probability to a compact carrying set does
not change the occupation law. -/
theorem productOccupationLaw_supportedRestriction
    {A V X : Type*} [MeasurableSpace A] [MeasurableSpace V] [MeasurableSpace X]
    (μ : ProbabilityMeasure A) (η : ProbabilityMeasure V) (K : Set V)
    (hK : MeasurableSet K) (hfull : ∀ᵐ z ∂(η : Measure V), z ∈ K)
    (p : A × V → X) (hp : Measurable p) :
    productOccupationLaw μ (supportedProbabilityRestriction η K hK hfull)
      (fun z => p (z.1, z.2.val)) = productOccupationLaw μ η p := by
  have hmap : ProbabilityMeasure.map (supportedProbabilityRestriction η K hK hfull)
      Subtype.val = η := by
    apply Subtype.ext
    exact supportedProbabilityRestriction_map η K hK hfull
  rw [← productOccupationLaw_map_right μ _ Subtype.val measurable_subtype_coe p hp, hmap]

/-- Evaluation at a fixed time is continuous in the topology of uniform
convergence on compact sets. -/
def flowTimeSlice {V : Type*} [TopologicalSpace V]
    (F : C(V × ℝ, V)) (T : ℝ) : C(V, V) :=
  F.comp ⟨fun z => (z, T), continuous_id.prodMk continuous_const⟩

theorem flowTimeSlice_tendsto
    {V ι : Type*} [TopologicalSpace V] {l : Filter ι}
    {Fs : ι → C(V × ℝ, V)} {F : C(V × ℝ, V)} (hF : Tendsto Fs l (𝓝 F)) (T : ℝ) :
    Tendsto (fun i => flowTimeSlice (Fs i) T) l (𝓝 (flowTimeSlice F T)) := by
  exact (ContinuousMap.continuous_precomp
    (⟨fun z => (z, T), continuous_id.prodMk continuous_const⟩ : C(V, V × ℝ))).continuousAt.tendsto.comp hF

end PolycyclicRecognition

end

end OAI
