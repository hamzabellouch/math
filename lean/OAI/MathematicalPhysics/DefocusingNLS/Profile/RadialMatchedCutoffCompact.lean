import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffProfileCompactApproximation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedProfileBounds

namespace OAI

/-! # Compact coefficient approximation for the constructed matched profile -/

open Filter Topology
open scoped SchwartzMap ContDiff

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialMatchedCutoff_compactApproximation (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (k : ℝ) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (L : ℕ → ℝ) (hL : ∀ j, 1 ≤ L j) (hLinf : Tendsto L atTop atTop) :
    let ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
    let hQ := radialMatchedCartesian_contDiff n z hX hz
    ExpandingCompactApproximation (radialShootingA n) k ha1 hk L hL (fun j =>
      schwartzTorusSample (radialShootingA n) k (L j) ha1 hk (hL j) (radianFourierKernel
        (cutoffProfileSchwartz (L j) (by linarith [hL j]) χ hχ (radialMatchedCartesian n z) hQ))) := by
  intro ha1 hQ
  exact cutoffProfile_compactApproximation (radialShootingA n) k
    (radialShootingA_bounds n (profileMatchingParameter z)).1 ha1 hk χ hχ hχzero hχone
    (radialMatchedCartesian n z) hQ (radialMatchedCartesian_finite_symbol n z hX hz) L hL hLinf

end DefocusingNLS

end OAI
