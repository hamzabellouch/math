import OAI.Geometry.SurfaceImmersion.Primitive.BoundaryProfileCoordinates

namespace OAI

/-! Compact five-profile estimates give an actual orthonormal normal frame
with the prescribed limiting coefficients for the exact immersion. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open RealModes SurfaceJetCoordinates JetVelocityCoordinates
open SurfaceVelocityFamily.Loop

def secondFormFrameGeometry {F : RField 4} {p : SmallModes.Base} {k : ℝ}
    (d : SecondFormFrame F p k) (z : ℝ) : (NormalFrame.Vec × NormalFrame.Vec) × (Fin 4 → ℝ) :=
  ((d.n,d.m),![d.S,d.D,d.N,z*d.L])

theorem compact_actual_frame_stability {K : Set EuclideanBoundaryProfile}
    (hK : IsCompact K) (hregular : ∀ J ∈ K, boundaryProfileMap J ∈ regularBoundaryProfiles)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ J ∈ K, ∀ F : RField 4, ContDiff ℝ ∞ F →
      ∀ z : ℝ, ∀ p : JetPolynomial.Base,
      ‖primitiveJetProfile (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) z p-J‖ ≤ δ →
      ∃ d : SecondFormFrame F (baseEquiv p)
        (coordinateGauss (realMetric F SmallModes.dx SmallModes.dx)
          (realMetric F SmallModes.dx SmallModes.dy) (realMetric F SmallModes.dy SmallModes.dy)
          (baseEquiv p)),
        ‖secondFormFrameGeometry d z-profileGeometry (boundaryProfileMap J)‖ < ε := by
  obtain ⟨δ,hδ,hclose⟩ := compact_euclidean_boundary_stability hK hregular ε hε
  refine ⟨δ,hδ,?_⟩
  intro J hJ F hF z p herror
  obtain ⟨hreg,hnear⟩ := hclose J hJ _ herror
  rw [boundaryProfileMap_chart hF] at hreg hnear
  obtain ⟨d,hn,hm,hcoef⟩ := exists_profile_secondFormFrame hF z (baseEquiv p) hreg
  refine ⟨d,?_⟩
  have heq : profileGeometry (realBoundaryProfile F z (baseEquiv p)) =
      secondFormFrameGeometry d z := by
    unfold profileGeometry secondFormFrameGeometry
    rw [← hn,← hm,hcoef]
  rwa [heq] at hnear

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
