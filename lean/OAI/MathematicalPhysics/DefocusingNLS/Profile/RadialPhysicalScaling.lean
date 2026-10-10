import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingInnerEquation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorShootingFamily
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhysicalFactor

namespace OAI

/-! Exact odd-power scaling for the physical radial exterior. -/

namespace DefocusingNLS
open ProfileCertificate

theorem radialShootingNu_physical (n : ℕ) (z : ProfileMatchingBall) :
    radialShootingNu (n+radialInnerShootingThreshold) z=
      -2*(radialShootingA n : ℂ)+2*Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ) := by
  unfold radialShootingNu radialShootingQ radialShootingA
  push_cast
  field_simp
  ring

theorem radialShootingA_power (n : ℕ) (w : RadialShootingDisk) :
    2*radialShootingA n*((n+radialInnerShootingThreshold : ℕ) : ℝ)=1 := by
  have hn : ((n+radialInnerShootingThreshold : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (radialShootingInner_power_pos n w))
  unfold radialShootingA
  field_simp

theorem radialPhysicalFactor_oddPower (k : ℕ) (hk : 0 < k) (b r : ℝ) (hr : 0 < r) (f : ℂ) :
    oddPowerNonlinearity k (Complex.exp ((-1/(k : ℂ)+2*Complex.I*(b : ℂ))*(Real.log r : ℂ))*f)=
      Complex.exp ((-1/(k : ℂ)+2*Complex.I*(b : ℂ))*(Real.log r : ℂ))/(r : ℂ)^2*
        oddPowerNonlinearity k f := by
  rw [oddPowerNonlinearity_eq,oddPowerNonlinearity_eq,norm_mul,mul_pow,
    radialPhysicalFactor_norm_power k hk b r hr]
  push_cast
  ring

end DefocusingNLS

end OAI
