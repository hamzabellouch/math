import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhaseSpectralMode
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTimeSpectralMode
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTranslationSpectralMode

namespace OAI

/-! All three symmetry eigenvalues have actual nonzero radial spectral modes. -/

namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialMatchedSymmetryMode (n ell N : ℕ) (hN : 7 ≤ N)
    (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (lam : ℂ)
    (hsym : (ell=0 ∧ (lam=0 ∨ lam=1)) ∨ (ell=1 ∧ lam=1/2)) :
    RadialSpectralMode (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) N (radialMatchedProfile n z) ((ell : ℂ)*(ell+10)) lam := by
  apply Classical.choice
  rcases hsym with ⟨rfl,rfl | rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨by simpa using radialMatchedPhaseMode n z hX hz N hN⟩
  · exact ⟨by simpa using radialMatchedTimeMode n z hX hz N hN⟩
  · exact ⟨by convert radialMatchedTranslationMode n z hX hz N hN using 1; norm_num⟩

end DefocusingNLS

end OAI
