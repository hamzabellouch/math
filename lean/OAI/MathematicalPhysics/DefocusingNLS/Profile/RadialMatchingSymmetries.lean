import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchingData
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhaseSpectralMode
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTranslationSpectralMode
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTimeSpectralMode

namespace OAI

/-! All symmetry values are zeros of the constructed actual matching determinant. -/

namespace DefocusingNLS
open ProfileCertificate

theorem RadialMatchingData.radial_symmetry_zeros {n : ℕ} {z : ProfileMatchingBall} {R L : ℝ}
    (d : RadialMatchingData n z 0 R L)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (hL : 1≤L) :
    d.determinant 0=0 ∧ d.determinant 1=0 := by
  have h0 : ‖(0 : ℂ)‖≤L := by simpa only [norm_zero] using (zero_le_one.trans hL)
  have h1 : ‖(1 : ℂ)‖≤L := by simpa only [norm_one] using hL
  constructor
  · apply d.mode_zero (N := 7) hX hz le_rfl 0 h0 (by norm_num)
    simpa only [Nat.zero_mul,Nat.cast_zero] using radialMatchedPhaseMode n z hX hz 7 le_rfl
  · apply d.mode_zero (N := 7) hX hz le_rfl 1 h1 (by norm_num)
    simpa only [Nat.zero_mul,Nat.cast_zero] using radialMatchedTimeMode n z hX hz 7 le_rfl

theorem RadialMatchingData.translation_zero {n : ℕ} {z : ProfileMatchingBall} {R L : ℝ}
    (d : RadialMatchingData n z 1 R L)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (hL : (1/2 : ℝ)≤L) : d.determinant (1/2)=0 := by
  have hhalf : ‖(1/2 : ℂ)‖≤L := by norm_num; exact hL
  apply d.mode_zero (N := 7) hX hz le_rfl (1/2) hhalf (by norm_num)
  convert radialMatchedTranslationMode n z hX hz 7 le_rfl using 1

end DefocusingNLS

end OAI
