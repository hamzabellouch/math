import OAI.Geometry.ProjectionBodies.AffineCovariance

namespace OAI

noncomputable section
open Set MeasureTheory
namespace PettyProjection

/-- The exact unrestricted inequality and its global equality characterization.
-/
theorem petty_projection_volume (n : ℕ) (hn : 4 ≤ n)
    (K : Set (Space n)) (hK : IsConvexBody K) :
    pettyConstant n ≤ projectionRatio K ∧
      (projectionRatio K = pettyConstant n ↔ IsEllipsoid K) := by
  obtain ⟨hbound,hrigid⟩ := projection_lower_bound hn hK
  exact ⟨hbound,hrigid,ellipsoid_projectionRatio (by omega)⟩

theorem mainClaim_proved : MainClaim := petty_projection_volume

theorem MainClaim_proved : MainClaim := mainClaim_proved

end PettyProjection
end

end OAI
