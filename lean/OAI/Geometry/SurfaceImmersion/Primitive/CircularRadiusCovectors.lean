import OAI.Geometry.SurfaceImmersion.Correction.SmoothCircularRadius
import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceRegularPair

namespace OAI

/-! The smooth radius fields used for Sard have exactly the true circle
normal covectors on the new boundaries. Their regular pairs are transverse. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

def circularNormalCovector (center base p : M) : CurvePlane :=
  phaseDerivative ((fun x => circularRadiusSquared (coordinateChart center center)
    (coordinateChart center x)) ∘ (coordinateChart base).symm) (coordinateChart base p)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma circularRadiusField_covector (i : A.centers) {r r0 : ℝ}
    (hsmall : r^2 < r0^2)
    (hpos : ∀ x, 0 < A.weight i x ↔ x ∈ circularCoordinateDisk (i : M) r0)
    {p q : M} (hp : p ∈ circularBoundary (i : M) r) (hq : p ∈ (chartAt Plane q).source) :
    phaseDerivative (A.circularRadiusField i ∘ (coordinateChart q).symm) (coordinateChart q p) =
      circularNormalCovector (i : M) q p := by
  have hqs : p ∈ (coordinateChart q).source := by simpa only [coordinateChart_source] using hq
  have ht : Tendsto (coordinateChart q).symm (𝓝 (coordinateChart q p)) (𝓝 p) := by
    simpa only [(coordinateChart q).left_inv hqs] using
      ((coordinateChart q).continuousAt_symm ((coordinateChart q).map_source hqs)).tendsto
  have he := (A.circularRadiusField_germ i
    (A.circularBoundary_weight_pos i hsmall hpos hp).ne').comp_tendsto ht
  unfold phaseDerivative circularNormalCovector
  rw [he.fderiv_eq]
  rfl

variable {ι : Type*} [Fintype ι]

lemma actual_circular_normals_independent
    (index : ι → A.centers) (r r0 : ι → ℝ) (i j : ι)
    (hsmall : ∀ k, (r k)^2 < (r0 k)^2)
    (hpos : ∀ k x, 0 < A.weight (index k) x ↔ x ∈ circularCoordinateDisk (index k : M) (r0 k))
    {p q : M} (hp : p ∈ circularBoundary (index i : M) (r i) ∩
      circularBoundary (index j : M) (r j)) (hq : p ∈ (chartAt Plane q).source)
    (hreg : Function.Surjective (fderiv ℝ (fun y => PublishedInputs.radiusPairProjection i j
      (fun k => A.circularRadiusField (index k) ((chartAt Plane q).symm y))) (chartAt Plane q p))) :
    covectorDet (circularNormalCovector (index i : M) q p)
      (circularNormalCovector (index j : M) q p) ≠ 0 := by
  have hh := surface_regular_pair_covectors (fun k => A.circularRadiusField (index k))
    (fun k => A.circularRadiusField_smooth (index k)) i j q hq hreg
  rw [A.circularRadiusField_covector (index i) (hsmall i) (hpos i) hp.1 hq,
    A.circularRadiusField_covector (index j) (hsmall j) (hpos j) hp.2 hq] at hh
  exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
