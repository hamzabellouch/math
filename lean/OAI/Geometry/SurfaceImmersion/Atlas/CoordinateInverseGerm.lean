import OAI.Geometry.SurfaceImmersion.Correction.SmoothingAtlas

namespace OAI

/-! Local inverse charts agree with the inverse of the assembled chart
near every common source point. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M]

theorem coordinate_inverse_germ (e d : OpenPartialHomeomorph M Base)
    {y : Base} (hy : y ∈ e.target) (hx : e.symm y ∈ d.source)
    (heq : EqOn d e d.source) :
    y ∈ d.target ∧ e.symm =ᶠ[𝓝 y] d.symm := by
  have hvalue : d (e.symm y) = y := (heq hx).trans (e.right_inv hy)
  have hyd : y ∈ d.target := hvalue ▸ d.map_source hx
  refine ⟨hyd,?_⟩
  filter_upwards [e.open_target.mem_nhds hy,
    e.symm.continuousAt hy |>.eventually (d.open_source.mem_nhds hx)] with z hz hzd
  calc
    e.symm z = d.symm (d (e.symm z)) := (d.left_inv hzd).symm
    _ = d.symm (e (e.symm z)) := congrArg d.symm (heq hzd)
    _ = d.symm z := congrArg d.symm (e.right_inv hz)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
