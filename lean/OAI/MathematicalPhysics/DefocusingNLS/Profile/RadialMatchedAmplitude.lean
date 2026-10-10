import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedVelocity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAmplitudePotentialDerivative

namespace OAI

/-! The actual amplitude and flow satisfy the real transport and potential identities. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedAmplitude_contDiffOn (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    ContDiffOn ℝ ∞ (fun r => ‖radialMatchedProfile n z r‖) (Ioi 0) :=
  (radialMatchedProfile_contDiffOn n z hX hz).norm ℝ
    (fun r hr => radialMatchedProfile_ne_zero n z hX r hr.le)

theorem radialMatchedVelocity_hasDerivAt (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : 0 < r) :
    let A := fun r => ‖radialMatchedProfile n z r‖
    let w := radialVelocity (6-2*radialShootingA n) A
    HasDerivAt w (6-2*radialShootingA n-11/r*w r-2*w r*deriv A r/A r) r := by
  dsimp only
  have hA := ((radialMatchedAmplitude_contDiffOn n z hX hz) r hr).contDiffAt
    (Ioi_mem_nhds hr)
  have hd := (hA.differentiableAt (by simp)).hasDerivAt
  have hc := (radialMatchedProfile_differentiable n z hX hz).continuous.norm
  have hn := norm_ne_zero_iff.mpr (radialMatchedProfile_ne_zero n z hX r hr.le)
  apply (radialVelocity_hasDerivAt_local _ _ _ hc r hr.ne' hn hd).congr_deriv
  dsimp only [radialVelocity]
  field_simp [hr.ne']

theorem radialMatchedPotential_hasDerivAt (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : 0 < r) :
    let A := fun r => ‖radialMatchedProfile n z r‖
    let c := 6-2*radialShootingA n
    let w := radialVelocity c A
    HasDerivAt (radialAmplitudePotential c (radialShootingB (profileMatchingParameter z)) A)
      (r*(1/8-c/2*(w r/r)+11/2*(w r/r)^2)+(w r)^2*deriv A r/A r) r := by
  dsimp only
  have hA := ((radialMatchedAmplitude_contDiffOn n z hX hz) r hr).contDiffAt
    (Ioi_mem_nhds hr)
  exact radialAmplitudePotential_hasDerivAt _ _ _ _
    (radialMatchedProfile_differentiable n z hX hz).continuous.norm r hr.ne'
    (norm_ne_zero_iff.mpr (radialMatchedProfile_ne_zero n z hX r hr.le))
    (hA.differentiableAt (by simp)).hasDerivAt

end DefocusingNLS

end OAI
