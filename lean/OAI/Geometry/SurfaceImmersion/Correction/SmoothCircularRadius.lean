import OAI.Geometry.SurfaceImmersion.Primitive.CircularBoundaryParam
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasJetCoordinateRelation

namespace OAI

/-! A smooth global radius field agrees with the actual squared coordinate
radius near every strictly smaller disk boundary. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
open JetPolynomial (planeCoordinateIsometry)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def circularRadiusField (i : A.centers) : M → ℝ :=
  restore (i : M) (A.outer i)
    (circularRadiusSquared (coordinateChart (i : M) (i : M)) ∘ planeCoordinateIsometry)

lemma circularRadiusField_smooth (i : A.centers) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (A.circularRadiusField i) :=
  restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
    ((circularRadiusSquared_smooth _).comp planeCoordinateIsometry.contDiff)

lemma circularRadiusField_germ (i : A.centers) {p : M} (hp : A.weight i p ≠ 0) :
    A.circularRadiusField i =ᶠ[𝓝 p]
      (fun x => circularRadiusSquared (coordinateChart (i : M) (i : M)) (coordinateChart (i : M) x)) := by
  have hs : p ∈ (chart (i : M)).source := A.weight_support i (subset_tsupport _ hp)
  filter_upwards [(chart (i : M)).open_source.mem_nhds hs,
    A.outer_eventually_one_of_weight_ne_zero i hp] with x hx ho
  simp only [circularRadiusField,restore,indicator_of_mem hx,ho,one_smul,Function.comp_apply]
  rfl

lemma circularBoundary_weight_pos (i : A.centers) {r r0 : ℝ}
    (hsmall : r^2 < r0^2)
    (hpos : ∀ x, 0 < A.weight i x ↔ x ∈ circularCoordinateDisk (i : M) r0)
    {p : M} (hp : p ∈ circularBoundary (i : M) r) : 0 < A.weight i p := by
  apply (hpos p).mpr
  exact ⟨hp.1,by change circularRadiusSquared _ _ < r0^2; rw [hp.2]; exact hsmall⟩

lemma circularBoundary_radiusField (i : A.centers) {r r0 : ℝ}
    (hsmall : r^2 < r0^2)
    (hpos : ∀ x, 0 < A.weight i x ↔ x ∈ circularCoordinateDisk (i : M) r0)
    {p : M} (hp : p ∈ circularBoundary (i : M) r) :
    A.circularRadiusField i p = r^2 := by
  rw [(A.circularRadiusField_germ i (A.circularBoundary_weight_pos i hsmall hpos hp).ne').eq_of_nhds]
  exact hp.2

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
