import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactProbabilityProduct
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProfileIncrementLimits

namespace OAI

/-! # Supported profile increments with an independent starting point -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

/-- The independent starting-point law need only have the specified point
in its support. The conclusion then holds at every supported profile. -/
theorem profile_increment_mem_of_independent_errors
    {U V W ι : Type*} [TopologicalSpace U] [LocallyCompactSpace U]
    [SecondCountableTopology U] [TopologicalSpace V] [LocallyCompactSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (S : Set C(V, W)) (hS : IsCompact S) (K : Set U) (hK : IsCompact K)
    [MeasurableSpace S] [BorelSpace S] [MeasurableSpace K] [BorelSpace K]
    (q : ℝ) (A : C(U, V)) {l : Filter ι} [l.NeBot]
    {T : ι → C(U, V)} {T₀ : C(U, V)} (hT : Tendsto T l (𝓝 T₀))
    (νs : ι → ProbabilityMeasure S) (ν : ProbabilityMeasure S)
    (hν : Tendsto νs l (𝓝 ν)) (η : ProbabilityMeasure K)
    {C : Set W} (hC : IsClosed C) (hne : C.Nonempty)
    (herr : Tendsto (fun i => ∫ f, ∫ z : K, Metric.infDist
      (q • (f.val (T i z.val) - f.val (A z.val))) C
      ∂(η : Measure K) ∂(νs i : Measure S)) l (𝓝 0))
    {f : S} (hf : f ∈ (ν : Measure S).support)
    {z : K} (hz : z ∈ (η : Measure K).support) :
    q • (f.val (T₀ z.val) - f.val (A z.val)) ∈ C := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let μs := fun i => productOccupationLaw (νs i) η id
  let μ := productOccupationLaw ν η id
  have hμ : Tendsto μs l (𝓝 μ) := productOccupationLaw_tendsto_fixed νs ν hν η
  have he : Tendsto (fun i => ∫ p, Metric.infDist
      (profileIncrementMap S K q A (T i) p) C ∂(μs i : Measure (S × K))) l (𝓝 0) := by
    let error := fun i => (⟨fun p => Metric.infDist (profileIncrementMap S K q A (T i) p) C,
      (Metric.continuous_infDist_pt C).comp
        (profileIncrementMap S K q A (T i)).continuous⟩ : C(S × K, ℝ))
    have heq (i : ι) := integral_productOccupationLaw (νs i) η id measurable_id (error i)
    simp only [Function.id_def] at heq
    exact herr.congr (fun i => (heq i).symm)
  exact profile_increment_mem_on_support S hS K hK q A hT μs μ hμ hC hne he
    (mem_support_productOccupationLaw ν η hf hz)

end PolycyclicRecognition

end

end OAI
