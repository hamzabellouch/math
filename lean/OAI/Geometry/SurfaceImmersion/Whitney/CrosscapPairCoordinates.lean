import OAI.Geometry.SurfaceImmersion.Whitney.StandardPreparedCrosscaps
import OAI.Geometry.SurfaceImmersion.Whitney.StandardCrosscapDerivative

namespace OAI

/-! The two branches of a double point near an actual prepared crosscap
are exactly the two opposite nonzero kernel-axis coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}
namespace SurfaceCrosscapCoordinates

theorem double_pair (c : SurfaceCrosscapCoordinates f p) {x y : M}
    (hx : x ∈ c.source.source) (hy : y ∈ c.source.source)
    (hne : x ≠ y) (heq : f x = f y) :
    c.source x 0 = 0 ∧ c.source y 0 = 0 ∧
      c.source x 1 = -c.source y 1 ∧ c.source x 1 ≠ 0 := by
  have hcne : c.source x ≠ c.source y := fun h => hne (c.source.injOn hx hy h)
  apply (standardCrosscap_double_iff hcne).mp
  apply c.target.injOn (c.model_mem x hx) (c.model_mem y hy)
  rw [← c.model_eq x hx,← c.model_eq y hy]
  exact heq

end SurfaceCrosscapCoordinates
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
