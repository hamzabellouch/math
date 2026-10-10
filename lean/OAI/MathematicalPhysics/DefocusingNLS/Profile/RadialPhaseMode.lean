import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialGaugeLinearization

namespace OAI

/-! The exact nonzero phase eigenmode of the finite-power matched profile. -/

open scoped ContDiff Laplacian
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialMatched_phaseMode (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (x : E) :
    similarityLinearization (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) (radialMatchedCartesian n z)
      (fun y => Complex.I*radialMatchedCartesian n z y) x=0 := by
  have h := radialMatched_splitGauge n z hX hz (fun _ : E => Complex.I) contDiff_const x
  dsimp only at h
  have he : (fun y => radialMatchedCartesian n z y*Complex.I)=
      (fun y => Complex.I*radialMatchedCartesian n z y) := by
    funext y
    exact mul_comm _ _
  rw [he] at h
  simpa [gaugeWeightedLaplacian,gaugeTransport] using h

theorem radialMatched_phaseMode_ne_zero (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (x : E) : Complex.I*radialMatchedCartesian n z x≠0 :=
  mul_ne_zero Complex.I_ne_zero
    (radialMatchedProfile_ne_zero n z hX ‖x‖ (norm_nonneg x))

end DefocusingNLS

end OAI
