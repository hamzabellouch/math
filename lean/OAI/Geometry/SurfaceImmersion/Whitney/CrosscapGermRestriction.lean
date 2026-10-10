import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapAxisCurve

namespace OAI

/-! An unchanged endpoint germ retains its actual crosscap chart after
 restricting the source neighborhood. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f g : M → ProjectionTarget 3} {p : M}

 theorem SurfaceCrosscapCoordinates.restrict_germ (C : SurfaceCrosscapCoordinates f p)
    (he : g =ᶠ[𝓝 p] f) :
    ∃ D : SurfaceCrosscapCoordinates g p, D.axisCurve = C.axisCurve := by
  obtain ⟨V,hV,hVO,hpV⟩ := mem_nhds_iff.mp he
  let c := C.source.restrOpen V hVO
  have hcp : p ∈ c.source := ⟨C.source_mem,hpV⟩
  have hcsub : c.source ⊆ C.source.source := inter_subset_left
  have hct : c.target ⊆ C.source.target := by
    intro x hx
    have hs : c.symm x ∈ c.source := c.map_target hx
    have heq : C.source (c.symm x) = x := c.right_inv hx
    rw [← heq]
    exact C.source.map_source (hcsub hs)
  let D : SurfaceCrosscapCoordinates g p := {
    source := c
    target := C.target
    source_mem := hcp
    source_center := C.source_center
    target_mem := C.target_mem
    target_center := C.target_center.trans he.self_of_nhds.symm
    source_smooth := C.source_smooth.mono hcsub
    source_inverse_smooth := C.source_inverse_smooth.mono hct
    target_smooth := C.target_smooth
    target_inverse_smooth := C.target_inverse_smooth
    model_mem := fun x hx => C.model_mem x (hcsub hx)
    model_eq := fun x hx => (hV hx.2).trans (C.model_eq x (hcsub hx)) }
  exact ⟨D,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
