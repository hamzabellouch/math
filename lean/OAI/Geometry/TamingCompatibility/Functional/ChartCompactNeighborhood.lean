import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianUnitMetric

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

omit [IsManifold Model ∞ X] in

lemma exists_compact_observer_neighborhood (p : X) {x : X}
    (hx : x ∈ (extChartAt Model p).source) {U : Set Space} (hU : IsOpen U)
    (hxU : extChartAt Model p x ∈ U) :
    ∃ K : Set Space, IsCompact K ∧ K ⊆ U ∧
      ∀ᶠ y in 𝓝 x, y ∈ (extChartAt Model p).source ∧ extChartAt Model p y ∈ K := by
  obtain ⟨K,hK,hzK,hKU⟩ := exists_compact_between
    (isCompact_singleton (x := extChartAt Model p x)) hU (singleton_subset_iff.mpr hxU)
  have hc := (continuousOn_extChartAt p).continuousAt ((isOpen_extChartAt_source p).mem_nhds hx)
  have hmem : K ∈ 𝓝 (extChartAt Model p x) := mem_of_superset
    (isOpen_interior.mem_nhds (hzK (mem_singleton _))) interior_subset
  refine ⟨K,hK,hKU,?_⟩
  filter_upwards [(isOpen_extChartAt_source p).mem_nhds hx,hc.eventually hmem] with y hy hz
  exact ⟨hy,hz⟩
end TamingCompatibility.GeometricChart

end
end

section

noncomputable section
namespace TamingCompatibility.ManifoldVolume
open ManifoldForms ManifoldHodge GeometricChart Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)

lemma compact_family_unit_lower {I : Type*} (β : I → smoothForms X 2)
    (hlocal : ∀ x : X, ∃ p : X, ∃ K : Set Space, ∃ C : ℝ,
      0 ≤ C ∧ (∀ᶠ y in 𝓝 x, y ∈ (extChartAt Model p).source ∧ extChartAt Model p y ∈ K) ∧
      ∀ i : I, ∀ z ∈ K, ∀ v : Space, chartMetric J α p z v v = 1 →
        -C ≤ ManifoldForms.pullback (β i).val (extChartAt Model p).symm z ![v,coordinateJ J p z v]) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : I, ∀ u : MetricUnit (hermitianMetric J α hs ht),
      -C ≤ unitEvaluation J (hermitianMetric J α hs ht) (β i).val (β i).property u := by
  let P : X → ℝ → Prop := fun x C => ∀ i : I, ∀ u : MetricUnit (hermitianMetric J α hs ht),
    u.val.proj = x → -C ≤ unitEvaluation J (hermitianMetric J α hs ht) (β i).val (β i).property u
  have hmono : ∀ x a b, a ≤ b → P x a → P x b := by
    intro x a b hab hx i u hu
    exact (neg_le_neg hab).trans (hx i u hu)
  have hloc : ∀ x ∈ (univ : Set X), ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, P y C := by
    intro x _
    obtain ⟨p,K,C,hC,hN,hbound⟩ := hlocal x
    refine ⟨C,hC,?_⟩
    filter_upwards [hN] with y hy
    intro i u hu
    apply unitEvaluation_lower_of_chart J α hs ht p (β i).val (β i).property (hbound i) u
    · simpa only [hu] using hy.1
    · simpa only [hu] using hy.2
  obtain ⟨C,hC,hbound⟩ := _root_.OAI.IsCompact.exists_uniform_monotone_bound isCompact_univ P hmono hloc
  exact ⟨C,hC,fun i u => hbound u.val.proj (mem_univ _) i u rfl⟩
end TamingCompatibility.ManifoldVolume

end
end

end
end

end OAI
