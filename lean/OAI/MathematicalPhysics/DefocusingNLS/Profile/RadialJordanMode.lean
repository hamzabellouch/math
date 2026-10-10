import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralMode
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialJordanChannels

namespace OAI

/-! A nontrivial classical radial Jordan pair with the actual finite-energy conditions. -/

open Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

def HasRadialJordanMode (n : ℕ) (z : ProfileMatchingBall) (ell N : ℕ) (lam : ℂ) : Prop :=
  ∃ u : RadialSpectralMode (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) N (radialMatchedProfile n z) ((ell : ℂ)*(ell+10)) lam,
    ∃ v w : ℝ → ℂ, ContDiff ℝ 2 v ∧ ContDiff ℝ 2 w ∧
      IsHarmonicRadialSourcePair (radialShootingA n) (radialShootingB (profileMatchingParameter z))
        (n+radialInnerShootingThreshold) (radialMatchedProfile n z) ((ell : ℂ)*(ell+10)) lam
        v w u.first u.second ∧
      IntegrableOn (fun r => r^11*‖iteratedDeriv N v r‖^2) (Ioi 0) ∧
      IntegrableOn (fun r => r^11*‖iteratedDeriv N w r‖^2) (Ioi 0) ∧
      ∃ M : ℝ, 0≤M ∧ ∀ r, ‖(v r,w r)‖≤M

theorem HasRadialJordanMode.radialMode {n ell N : ℕ} {z : ProfileMatchingBall} {lam : ℂ}
    (h : HasRadialJordanMode n z ell N lam) :
    Nonempty (RadialSpectralMode (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) N (radialMatchedProfile n z) ((ell : ℂ)*(ell+10)) lam) := by
  obtain ⟨u,_⟩ := h
  exact ⟨u⟩

end DefocusingNLS

end OAI
