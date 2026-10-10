import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceCompactCoordinateMap
import OAI.Geometry.SurfaceImmersion.Correction.CompactSurfaceSmoothExtension
import OAI.Geometry.SurfaceImmersion.Whitney.ArcTimeChartPartition

namespace OAI

/-! A regular coordinate map on a compact set gives a time chart,
retaining its prescribed longitudinal coordinate on the whole source. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M] [Nonempty M]

theorem compact_time_chart {K U : Set M} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {f : M → Base} {F : M → ℝ}
    (hf : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ f U)
    (htime : ∀ x ∈ U, f x 1 = F x) (hi : K.InjOn f)
    (hreg : ∀ x ∈ K, Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base) f x)) :
    ∃ c : SurfaceTimeChart F, K ⊆ c.coord.source ∧ EqOn c.coord f c.coord.source := by
  obtain ⟨g,V,hg,hV,hKV,hVU,heq⟩ := compact_surface_smooth_extension hK hU hKU hf
  have hgi : K.InjOn g := by
    intro x hx y hy hxy
    apply hi hx hy
    simpa only [← heq (hKV hx),← heq (hKV hy)] using hxy
  have hgr : ∀ x ∈ K, Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base) g x) := by
    intro x hx
    rw [(heq.eventuallyEq_of_mem (hV.mem_nhds (hKV hx))).mfderiv_eq]
    exact hreg x hx
  obtain ⟨d,hKd,hd,hdi⟩ := surface_compact_coordinate_map hg hK hgi hgr
  let e := d.restrOpen V hV
  have hes : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ e e.source := by
    change ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ d (d.source ∩ V)
    rw [hd]
    exact hg.contMDiffOn
  refine ⟨⟨e,hes,hdi.mono (fun _ hx => hx.1),?_⟩,?_,?_⟩
  · intro x hx
    change d x 1 = F x
    rw [hd,heq hx.2]
    exact htime x (hVU hx.2)
  · intro x hx
    exact ⟨hKd hx,hKV hx⟩
  · intro x hx
    change d x = f x
    rw [hd]
    exact heq hx.2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
