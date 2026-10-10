import OAI.Geometry.SurfaceImmersion.Primitive.CircularSectionProfiles
import OAI.Geometry.SurfaceImmersion.Primitive.PhaseLeadingProfileStability

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

def phaseRealChartMap (i : A.centers) (T : JetPolynomial.Base → JetPolynomial.Base) (F : M → Space) : RField 4 :=
  A.jetChartMap i F ∘ T ∘ baseEquiv.symm

lemma phaseRealChartMap_smooth (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ContDiff ℝ ∞ (A.phaseRealChartMap i T F) :=
  (A.jetChartMap_smooth i hF).comp (hT.comp baseEquiv.symm.contDiff)

lemma phaseRealChartMap_profile (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (z : ℝ) (p : JetPolynomial.Base) :
    boundaryProfileMap (SurfaceVelocityFamily.Loop.primitiveJetProfile (A.vectorChartRead i F ∘ T) z p) =
      realBoundaryProfile (A.phaseRealChartMap i T F) z (baseEquiv p) := by
  have he : (fun q => JetVelocityCoordinates.toEuclidean (A.phaseRealChartMap i T F (baseEquiv q))) =
      A.vectorChartRead i F ∘ T := by
    funext q
    change spaceCoordinates.symm
      (A.jetChartMap i F (T (baseEquiv.symm (baseEquiv q)))) = A.vectorChartRead i F (T q)
    rw [baseEquiv.symm_apply_apply]
    exact spaceCoordinates.symm_apply_apply _
  simpa only [he] using boundaryProfileMap_chart (A.phaseRealChartMap_smooth i hT hF) z p

/-- The exact primitive's Euclidean profile estimate gives the real-coordinate
estimate used by the boundary preservation lemmas. -/
lemma phaseRealChartMap_profile_error (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (z : ℝ) (p : JetPolynomial.Base)
    (J : EuclideanBoundaryProfile) {ε : ℝ} (hε : 0 < ε)
    (hclose : ‖SurfaceVelocityFamily.Loop.primitiveJetProfile (A.vectorChartRead i F ∘ T) z p - J‖ <
      ε / (‖boundaryProfileMap‖ + 1)) :
    ‖realBoundaryProfile (A.phaseRealChartMap i T F) z (baseEquiv p) - boundaryProfileMap J‖ < ε := by
  rw [← A.phaseRealChartMap_profile i hT hF z p, ← map_sub]
  calc
    ‖boundaryProfileMap _‖ ≤ ‖boundaryProfileMap‖ *
        ‖SurfaceVelocityFamily.Loop.primitiveJetProfile (A.vectorChartRead i F ∘ T) z p - J‖ :=
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
