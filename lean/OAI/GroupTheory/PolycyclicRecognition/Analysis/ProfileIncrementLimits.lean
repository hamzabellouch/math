import OAI.GroupTheory.PolycyclicRecognition.Geometry.ProfileFlowConvergence
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportedProfileConstraints

namespace OAI

/-! # Supported increment constraints from actual converging chart flows -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology

variable {U V W : Type*} [TopologicalSpace U] [LocallyCompactSpace U]
  [TopologicalSpace V] [LocallyCompactSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A normalized increment of a profile between two coordinate maps. -/
def profileIncrementMap (S : Set C(V, W)) (K : Set U) (q : ℝ)
    (A T : C(U, V)) : C(S × K, W) :=
  q • (profileAlongMap S K T - profileAlongMap S K A)

/-- The increment observable is continuous in the endpoint map. -/
theorem continuous_profileIncrementMap (S : Set C(V, W)) (K : Set U) (q : ℝ)
    (A : C(U, V)) : Continuous (profileIncrementMap S K q A) := by
  exact (continuous_const : Continuous (fun _ : C(U, V) => q)).smul
    ((continuous_profileAlongMap S K).sub continuous_const)

/-- Varying endpoint maps give uniformly convergent increment observables
on a compact profile family and compact starting-point set. -/
theorem profileIncrementMap_tendstoUniformly
    (S : Set C(V, W)) (hS : IsCompact S) (K : Set U) (hK : IsCompact K)
    (q : ℝ) (A : C(U, V)) {ι : Type*} {l : Filter ι}
    {T : ι → C(U, V)} {T₀ : C(U, V)} (hT : Tendsto T l (𝓝 T₀)) :
    TendstoUniformly (fun i p => profileIncrementMap S K q A (T i) p)
      (profileIncrementMap S K q A T₀) l := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have ht : Tendsto (fun i => profileIncrementMap S K q A (T i)) l
      (𝓝 (profileIncrementMap S K q A T₀)) := by
    simpa only [Function.comp_def] using
      ((continuous_profileIncrementMap S K q A).tendsto T₀).comp hT
  exact tendstoUniformlyOn_univ.mp
    ((ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp ht) univ isCompact_univ)

/-- A vanishing expected distance for the actual scaled endpoints forces
the limiting segment increment to satisfy the constraint at every supported
profile and starting point. -/
theorem profile_increment_mem_on_support
    (S : Set C(V, W)) (hS : IsCompact S) (K : Set U) (hK : IsCompact K)
    [MeasurableSpace (S × K)] [BorelSpace (S × K)]
    (q : ℝ) (A : C(U, V)) {ι : Type*} {l : Filter ι} [l.NeBot]
    {T : ι → C(U, V)} {T₀ : C(U, V)} (hT : Tendsto T l (𝓝 T₀))
    (μs : ι → ProbabilityMeasure (S × K)) (μ : ProbabilityMeasure (S × K))
    (hμ : Tendsto μs l (𝓝 μ)) {C : Set W} (hC : IsClosed C) (hne : C.Nonempty)
    (herr : Tendsto (fun i => ∫ p, Metric.infDist
      (profileIncrementMap S K q A (T i) p) C ∂(μs i : Measure (S × K))) l (𝓝 0))
    {p : S × K} (hp : p ∈ (μ : Measure (S × K)).support) :
    q • (p.1.val (T₀ p.2.val) - p.1.val (A p.2.val)) ∈ C := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact mem_on_support_of_uniformly_vanishing_distance μs μ hμ
    (fun i => profileIncrementMap S K q A (T i)) (profileIncrementMap S K q A T₀)
    (profileIncrementMap_tendstoUniformly S hS K hK q A hT) hC hne herr hp

end PolycyclicRecognition

end

end OAI
