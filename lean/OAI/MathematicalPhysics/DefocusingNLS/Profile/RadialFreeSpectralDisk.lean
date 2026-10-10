import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeShootingData
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeLowAngularSpectrum

namespace OAI

/-! The actual limiting shooting parameters lie in the same exact disk used
by the free spectral certificates. -/

namespace DefocusingNLS
open ProfileCertificate

theorem radialShootingR_sq (w : RadialShootingDisk) :
    (radialShootingR w)^2/4=radialShootingZ w := by
  have hz := (disk_coordinates w).2
  have hzpos : 0≤radialShootingZ w := by
    have hh := (abs_le.mp hz).1
    norm_num [radius,centerZ] at hh
    dsimp only [radialShootingZ]
    norm_num [centerZ]
    linarith
  dsimp only [radialShootingR]
  rw [mul_pow,Real.sq_sqrt hzpos]
  ring

theorem radialShooting_freeMatchingDisk (w : RadialShootingDisk) :
    (radialShootingB w,(radialShootingR w)^2/4)∈freeMatchingDisk := by
  rw [radialShootingR_sq]
  have hw : ‖w.val‖≤(radius : ℝ) := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using w.property
  have hs := (sq_le_sq₀ (norm_nonneg w.val) (by norm_num [radius] : (0 : ℝ)≤radius)).mpr hw
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply] at hs
  simpa [freeMatchingDisk,radialShootingB,radialShootingZ,centerB,centerZ,radius,pow_two] using hs

end DefocusingNLS

end OAI
