import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCompactExclusion
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeSpectralDisk
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeOutgoingNonvanishing

namespace OAI

/-! In each fixed angular degree at least two, actual matched eigenvalues
eventually leave every compact subset of the counting half-plane. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedSpectralMode_nonradial_compact_exclusion
    (hR : RectangleRouche) (ell N : ℕ) (hell : 2≤ell) (hN : 7≤N)
    (K : Set ℂ) (hK : IsCompact K) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ lam ∈ K, -(1/32 : ℝ)≤lam.re →
      ¬ Nonempty (RadialSpectralMode (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold) N
        (radialMatchedProfile n z) ((ell : ℂ)*(ell+10)) lam) := by
  apply radialMatchedSpectralMode_compact_exclusion ell N hN K hK
  intro z _ _ lam _ hhalf
  exact free_outgoing_nonzero hR ell hell _ _
    (radialShooting_freeMatchingDisk (profileMatchingParameter z)) lam hhalf

end DefocusingNLS

end OAI
