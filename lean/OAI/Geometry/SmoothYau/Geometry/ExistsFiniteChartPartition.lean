import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

theorem exists_finite_chart_partition :
    ∃ t : Finset M, ∃ ρ : SmoothPartitionOfUnity t 𝓘(ℝ, E) M univ,
      ρ.IsSubordinate (fun i => (chartAt E (i : M)).source) := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun p : M => (chartAt E p).source) (fun p => (chartAt E p).open_source)
    (by intro x _; exact mem_iUnion_of_mem x (mem_chart_source E x))
  refine ⟨t, ?_⟩
  apply SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, E)) isClosed_univ
    (fun i : t => (chartAt E (i : M)).source) (fun i => (chartAt E (i : M)).open_source)
  intro x hx
  obtain ⟨p, hp, hpx⟩ := mem_iUnion₂.mp (ht hx)
  exact mem_iUnion_of_mem ⟨p, hp⟩ hpx

end YauCounterexamples

end

end OAI
