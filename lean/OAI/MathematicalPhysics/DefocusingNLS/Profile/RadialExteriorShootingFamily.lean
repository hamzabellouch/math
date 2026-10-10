import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorShootingData
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorCompactLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorCanonicalContinuity

namespace OAI

/-! The actual outgoing boundary family on the full compact matching ball. -/

open Filter
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialShootingNu (n : ℕ) (z : ProfileMatchingBall) : ℂ :=
  -2*radialShootingQ z-1/(n : ℂ)

noncomputable def radialShootingExteriorJet (n : ℕ) (z : ProfileMatchingBall) : ℂ × ℂ :=
  radialExteriorCanonical (radialShootingNu n z) n (radialShootingM z)
    (Real.log innerBoundaryRadius) (Real.log innerBoundaryRadius)

theorem radialShootingExterior_exists :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu n z) n (radialShootingM z)
        (Real.log innerBoundaryRadius) := by
  exact radialExterior_compact_exists radialShootingQ radialShootingM
    continuous_radialShootingQ continuous_radialShootingM (Real.log innerBoundaryRadius)
    (fun z => by simp [radialShootingQ]) radialShooting_free_annulus

theorem radialShootingExterior_continuous :
    ∀ᶠ n in atTop, Continuous (radialShootingExteriorJet n) := by
  filter_upwards [radialShootingExterior_exists] with n hn
  exact continuous_radialExteriorCanonical_boundary n (radialShootingNu n) radialShootingM
    ((continuous_const.mul continuous_radialShootingQ).sub continuous_const)
    continuous_radialShootingM radialShootingM_ne_zero (Real.log innerBoundaryRadius) hn

theorem radialShootingExterior_limit :
    TendstoUniformly radialShootingExteriorJet
      (fun z => radialFreeSlowJet (radialShootingQ z) (radialShootingM z)
        (Real.log innerBoundaryRadius)) atTop := by
  exact radialExterior_compact_boundary_limit radialShootingQ radialShootingM
    continuous_radialShootingQ continuous_radialShootingM (Real.log innerBoundaryRadius)
    (fun z => by simp [radialShootingQ]) radialShooting_free_annulus

end DefocusingNLS

end OAI
