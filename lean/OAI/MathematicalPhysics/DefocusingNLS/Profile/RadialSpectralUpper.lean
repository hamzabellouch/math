import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousAngularUpper
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralMode

namespace OAI

/-! The real-part bound applies directly to the actual nonzero radial modes. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedSpectralMode_re_lt_four :
    ∀ᶠ n : ℕ in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ ell N : ℕ, 7≤N → ∀ lam : ℂ,
      RadialSpectralMode (radialShootingA n) (radialShootingB (profileMatchingParameter z))
        (n+radialInnerShootingThreshold) N (radialMatchedProfile n z)
        ((ell : ℂ)*(ell+10)) lam → lam.re<4 := by
  filter_upwards [homogeneous_matched_angular_upper] with n hn z hX hz ell N hN lam mode
  by_contra h
  have hη : (((ell : ℝ)*(ell+10) : ℝ) : ℂ)=(ell : ℂ)*(ell+10) := by push_cast; rfl
  have hzero := hn z hX hz ((ell : ℝ)*(ell+10)) (by positivity) N hN lam
    (not_lt.mp h) mode.first mode.second mode.first_c2 mode.second_c2
    (by simpa only [hη] using mode.equation) mode.bounded mode.first_top mode.second_top
  obtain ⟨r,hr,hne⟩ := mode.nonzero
  exact hne.elim (fun hf => hf (hzero r hr.le).1) (fun hg => hg (hzero r hr.le).2)

end DefocusingNLS

end OAI
