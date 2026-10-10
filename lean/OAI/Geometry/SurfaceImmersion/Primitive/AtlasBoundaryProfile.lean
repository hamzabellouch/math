import OAI.Geometry.SurfaceImmersion.Primitive.CircularSectionProfiles
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasLeadingProfileStability

namespace OAI

/-! Read the exact immersion's five profiles in the real coordinate chart
used by the Gauss and boundary calculations. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates GeometryPreservation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def realChartMap (i : A.centers) (F : M → Space) : RField 4 :=
  A.jetChartMap i F ∘ baseEquiv.symm

lemma realChartMap_smooth (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ContDiff ℝ ∞ (A.realChartMap i F) :=
  (A.jetChartMap_smooth i hF).comp baseEquiv.symm.contDiff

lemma realChartMap_profile (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (z : ℝ) (p : JetPolynomial.Base) :
    boundaryProfileMap (SurfaceVelocityFamily.Loop.primitiveJetProfile (A.vectorChartRead i F) z p) =
      realBoundaryProfile (A.realChartMap i F) z (baseEquiv p) := by
  have he : (fun q => JetVelocityCoordinates.toEuclidean (A.realChartMap i F (baseEquiv q))) =
      A.vectorChartRead i F := by
    funext q
    change spaceCoordinates.symm
      (A.jetChartMap i F (baseEquiv.symm (baseEquiv q))) = A.vectorChartRead i F q
    rw [baseEquiv.symm_apply_apply]
    exact spaceCoordinates.symm_apply_apply _
  simpa only [he] using boundaryProfileMap_chart (A.realChartMap_smooth i hF) z p

/-- The exact primitive's Euclidean profile estimate gives the real-coordinate
estimate used by the boundary preservation lemmas. -/
lemma realChartMap_profile_error (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (z : ℝ) (p : JetPolynomial.Base)
    (J : EuclideanBoundaryProfile) {ε : ℝ} (hε : 0 < ε)
    (hclose : ‖SurfaceVelocityFamily.Loop.primitiveJetProfile (A.vectorChartRead i F) z p - J‖ <
      ε / (‖boundaryProfileMap‖ + 1)) :
    ‖realBoundaryProfile (A.realChartMap i F) z (baseEquiv p) - boundaryProfileMap J‖ < ε := by
  rw [← A.realChartMap_profile i hF z p, ← map_sub]
  calc
    ‖boundaryProfileMap _‖ ≤ ‖boundaryProfileMap‖ *
        ‖SurfaceVelocityFamily.Loop.primitiveJetProfile (A.vectorChartRead i F) z p - J‖ :=
      boundaryProfileMap.le_opNorm _
    _ < (‖boundaryProfileMap‖ + 1) * (ε / (‖boundaryProfileMap‖ + 1)) := by
      have hn := norm_nonneg boundaryProfileMap
      have hd : 0 < ‖boundaryProfileMap‖ + 1 := by positivity
      have he : 0 < ε / (‖boundaryProfileMap‖ + 1) := div_pos hε hd
      nlinarith [mul_le_mul_of_nonneg_left hclose.le hn]
    _ = ε := mul_div_cancel₀ ε (by positivity)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
