import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralClassification
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCompactJordanExclusion

namespace OAI

/-! Uniform absence of generalized radial eigenvectors in the counting half-plane. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_no_jordan (hRou : RectangleRouche) (N : ℕ) (hN : 7 ≤ N) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ ell : ℕ, ∀ lam : ℂ, -(1/32 : ℝ) ≤ lam.re →
      ¬ HasRadialJordanMode n z ell N lam := by
  let K : Set ℂ := {0, 1, 1/2}
  have hK : IsCompact K := (Set.toFinite K).isCompact
  filter_upwards [radialMatchedSpectralMode_classification hRou N hN,
    radialMatched_no_jordan_compact hRou 0 N hN K hK,
    radialMatched_no_jordan_compact hRou 1 N hN K hK] with n hc h0 h1
  intro z hX hz ell lam hl hj
  have heq : (((ell : ℝ)*(ell+10) : ℝ) : ℂ)=(ell : ℂ)*(ell+10) := by push_cast; rfl
  have hm := hj.radialMode
  have hs := hc z hX hz ell lam hl (by simpa only [heq] using hm)
  rcases hs with ⟨rfl,rfl | rfl⟩ | ⟨rfl,rfl⟩
  · exact h0 z hX hz 0 (by simp [K]) hl hj
  · exact h0 z hX hz 1 (by simp [K]) hl hj
  · exact h1 z hX hz (1/2) (by simp [K]) hl hj

end DefocusingNLS

end OAI
