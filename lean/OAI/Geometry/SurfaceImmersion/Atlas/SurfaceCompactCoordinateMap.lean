import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceLocalCoordinateMap
import OAI.Geometry.SurfaceImmersion.Atlas.CompactLocalChart
import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateInverseGerm

namespace OAI

/-! A smooth coordinate map regular and injective on a compact surface
set is one smooth chart on a neighborhood of that set. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [Nonempty M]

theorem surface_compact_coordinate_map {f : M → Base}
    (hf : ContMDiff planeModel 𝓘(ℝ,Base) ∞ f) {K : Set M}
    (hK : IsCompact K) (hi : K.InjOn f)
    (hreg : ∀ x ∈ K, Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base) f x)) :
    ∃ e : OpenPartialHomeomorph M Base, K ⊆ e.source ∧ (e : M → Base) = f ∧
      ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ e.symm e.target := by
  obtain ⟨e,hKe,he,hcover⟩ := compact_local_chart_with_property
    (fun d : OpenPartialHomeomorph M Base => ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ d.symm d.target)
    hf.continuous hK hi (by
      intro x hx
      obtain ⟨d,hd,heq,_,hdi⟩ := surface_local_coordinate_map hf x (hreg x hx)
      exact ⟨d,hd,heq,hdi⟩)
  refine ⟨e,hKe,he,?_⟩
  intro y hy
  obtain ⟨d,hd,heq,hdi⟩ := hcover (e.symm y) (e.map_target hy)
  have hde : EqOn d e d.source := by intro x hx; rw [he]; exact heq hx
  obtain ⟨hyd,hgerm⟩ := coordinate_inverse_germ e d hy hd hde
  exact ((hdi.contMDiffAt (d.open_target.mem_nhds hyd)).congr_of_eventuallyEq hgerm).contMDiffWithinAt

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
