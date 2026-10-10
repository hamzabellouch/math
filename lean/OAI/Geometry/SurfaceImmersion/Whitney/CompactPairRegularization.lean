import OAI.Geometry.SurfaceImmersion.Whitney.FiniteSurfacePairRegularization

namespace OAI

/-! Regularize any compact collection of distinct pairs outside the
frozen diagonal squares, while keeping the map uniformly close and
unchanged up to translations near the frozen closed sets. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] [Fintype ι]

theorem compact_pair_regularization
    (A : ι → Set M) (hA : ∀ i, IsClosed (A i)) (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    {K : Set (M × M)} (hK : IsCompact K)
    (hne : ∀ z ∈ K, z.1 ≠ z.2)
    (hout : ∀ z ∈ K, ∀ i, ¬ (z.1 ∈ A i ∧ z.2 ∈ A i))
    {f : M → ProjectionTarget 3} (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      FrozenTranslationGerms A f g ∧ (∀ x, ‖g x-f x‖ < ε) ∧
      ∀ z ∈ K, g z.1 = g z.2 → Function.Surjective (surfacePairDerivative g z.1 z.2) := by
  obtain ⟨P,T,s,hT,hcover,hPA⟩ := finite_pair_patch_cover A hA hdis hK hne hout
  obtain ⟨g,hg,hfg,hclose,hgood⟩ := finite_surface_pair_regularization
    (fun z : K => z.val.1) (fun z : K => z.val.2) P T
    (fun z => (hT z).1) (fun z x hx => ((hT z).2 hx).2) A hPA s hf hε
  refine ⟨g,hg,hfg,hclose,?_⟩
  intro z hz
  obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp (hcover hz)
  exact hgood i hi z hzi

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
