import OAI.GroupTheory.PolycyclicRecognition.Analysis.IndependentProfileLimits
import OAI.GroupTheory.PolycyclicRecognition.Geometry.OccupationFlowLimit

namespace OAI

/-! # Convex increments of supported sampled profiles -/

noncomputable section

namespace PolycyclicRecognition

open Filter MeasureTheory Set Metric
open scoped Topology NNReal

/-- The two-limit occupation estimate implies the increment constraint for
every supported profile. Sampling, the exact cocycle identity, and domination
are stated separately so that all are checked on the actual chart. -/
theorem sampled_profile_increment_mem
    {U V W A G ι : Type*}
    [TopologicalSpace U] [LocallyCompactSpace U] [SecondCountableTopology U]
    [TopologicalSpace V] [LocallyCompactSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [Group G] [MetricSpace G] [ProperSpace G] [IsTopologicalGroup G]
    [IsIsometricSMul G G] [MeasurableSpace A]
    {Λ Kπ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)]
    [BorelSpace (NormalizedPair G Λ)]
    (S : Set C(V, W)) (hS : IsCompact S) (K : Set U) (hK : IsCompact K)
    [MeasurableSpace S] [BorelSpace S] [MeasurableSpace K] [BorelSpace K]
    (π : G →* Multiplicative W) (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    {l : Filter ι} [l.NeBot] (samples : ι → ProbabilityMeasure A)
    (profile : ι → A → S) (hprofile : ∀ i, Measurable (profile i))
    (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun i => ProbabilityMeasure.map (samples i) (profile i)) l (𝓝 ν))
    (η : ProbabilityMeasure K)
    (chart : ι → A × K → NormalizedPair G Λ) (hchart : ∀ i, Measurable (chart i))
    (μs : ι → ProbabilityMeasure (NormalizedPair G Λ))
    (μ : ProbabilityMeasure (NormalizedPair G Λ)) (hμ : Tendsto μs l (𝓝 μ))
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (t : ι → ℝ) (ht : Tendsto t l atTop) (c : ℝ≥0)
    (hdom : ∀ L : ℕ, 0 < L → ∀ᶠ i in l, ∀ j : Fin ⌊t i / (L : ℝ)⌋₊,
      Measure.map (fun p : NormalizedPair G Λ => (d L ^ (j : ℕ))⁻¹ • p)
        (productOccupationLaw (samples i) η (chart i) : Measure _) ≤ c • (μs i : Measure _))
    (q : ℝ) (start : C(U, V)) (ends : ι → C(U, V)) (end₀ : C(U, V))
    (hends : Tendsto ends l (𝓝 end₀))
    (hidentity : ∀ i, ∀ᵐ a ∂(samples i : Measure A), ∀ z,
      (t i)⁻¹ • pairHeight π (d (t i)) (chart i (a, z)) =
      q • ((profile i a).val (ends i z.val) - (profile i a).val (start z.val)))
    {B : Set W} (hB : IsCompact B) {b : W} (hb : b ∈ B)
    (hconvex : IsClosed (convexHull ℝ B))
    (hstationary : Tendsto (fun L : ℕ => ∫ p : NormalizedPair G Λ,
      infDist ((L : ℝ)⁻¹ • pairHeight π (d L) p) B ∂(μ : Measure _)) atTop (𝓝 0))
    {f : S} (hf : f ∈ (ν : Measure S).support)
    {z : K} (hz : z ∈ (η : Measure K).support) :
    q • (f.val (end₀ z.val) - f.val (start z.val)) ∈ convexHull ℝ B := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let σ := fun i => productOccupationLaw (samples i) η (chart i)
  have herror := normalized_flow_error_tendsto_zero π hπ σ μs μ hμ d hd hd0 hmul
    t ht c hdom hB hb hstationary
  apply profile_increment_mem_of_independent_errors S hS K hK q start hends
    (fun i => ProbabilityMeasure.map (samples i) (profile i)) ν hν η
    hconvex ⟨b, subset_convexHull ℝ B hb⟩ _ hf hz
  have heq (i : ι) :
      (∫ f, ∫ z : K, infDist (q • (f.val (ends i z.val) - f.val (start z.val)))
          (convexHull ℝ B) ∂(η : Measure K)
        ∂(ProbabilityMeasure.map (samples i) (profile i) : Measure S)) =
      ∫ p, infDist ((t i)⁻¹ • pairHeight π (d (t i)) p) (convexHull ℝ B)
        ∂(σ i : Measure (NormalizedPair G Λ)) := by
    let error : C(S × K, ℝ) := ⟨fun p => infDist
      (profileIncrementMap S K q start (ends i) p) (convexHull ℝ B),
      (continuous_infDist_pt _).comp (profileIncrementMap S K q start (ends i)).continuous⟩
    change (∫ f, ∫ z : K, error (id (f, z)) ∂(η : Measure K)
      ∂(ProbabilityMeasure.map (samples i) (profile i) : Measure S)) = _
    rw [← integral_productOccupationLaw _ η id measurable_id error,
      productOccupationLaw_map_left _ η _ (hprofile i),
      integral_productOccupationLaw _ η _ ((hprofile i).prodMap measurable_id) error]
    let pairError : C(NormalizedPair G Λ, ℝ) :=
      ⟨_, continuous_pair_label_distance π hπ.continuous (d (t i)) (t i) (convexHull ℝ B)⟩
    change (∫ a, ∫ z, error (Prod.map (profile i) id (a, z)) ∂(η : Measure K)
      ∂(samples i : Measure A)) =
      ∫ p, pairError p ∂(productOccupationLaw (samples i) η (chart i) : Measure _)
    rw [integral_productOccupationLaw _ η _ (hchart i) pairError]
    apply integral_congr_ae
    filter_upwards [hidentity i] with a ha
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by
        change infDist (q • ((profile i a).val (ends i z.val) -
          (profile i a).val (start z.val))) (convexHull ℝ B) =
          infDist ((t i)⁻¹ • pairHeight π (d (t i)) (chart i (a, z))) (convexHull ℝ B)
        rw [ha])
  exact herror.congr (fun i => (heq i).symm)

end PolycyclicRecognition

end

end OAI
