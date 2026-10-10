import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFixedRadialModes
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralNoJordan

namespace OAI

/-! The actual contour generator has precisely the symmetry spectrum and no Jordan chains. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialMatched_contour_spectral_stability (hRou : RectangleRouche) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius)) →
      (hz : radialMatchingMap n z=0) → ∀ (N : ℕ)
    (ha : 0 < radialShootingA n) (ha1 : radialShootingA n < 1) (hk : 8 < (N : ℝ))
    (q : HomogeneousY (radialShootingA n) N)
    (_hq : ∀ x : E, homogeneousPhysicalCLM (radialShootingA n) N ha ha1 hk q x =
      radialMatchedCartesian n z x)
    (P : (HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N) →L[ℂ]
      (HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N))
    (hcomm : ∀ t, Commute (homogeneousComplexLinearizedStep (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
      (n + radialInnerShootingThreshold) q t) P)
    (_hfin : FiniteDimensional ℂ P.range) (G : P.range →L[ℂ] P.range)
    (_hG : ∀ t, projectionSemigroupRestriction
      (homogeneousComplexLinearizedStep (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
        (n + radialInnerShootingThreshold) q) P hcomm t = NormedSpace.exp ((t : ℝ) • G)),
      (∀ (lam : ℂ) (w : P.range), w ≠ 0 → G w=lam • w →
        -(1/32 : ℝ) ≤ lam.re → lam=0 ∨ lam=1 ∨ lam=1/2) ∧
      (∀ (lam : ℂ) (v w : P.range), w ≠ 0 → G w=lam • w →
        -(1/32 : ℝ) ≤ lam.re → G v ≠ lam • v+w) := by
  filter_upwards [radialMatchedSpectralMode_classification hRou 9 (by omega),
    radialMatched_no_jordan hRou 9 (by omega)] with n hc hj
  intro z hX hz N ha ha1 hk q hq P hcomm hfin G hG
  constructor
  · intro lam w hw he hl
    obtain ⟨ell,hu⟩ := homogeneous_matched_contour_radialMode_fixed n z hX hz N
      ha ha1 hk q hq P hcomm hfin G hG lam w hw he
    have heq : (((ell : ℝ)*(ell+10) : ℝ) : ℂ)=(ell : ℂ)*(ell+10) := by push_cast; rfl
    have hs := hc z hX hz ell lam hl (by simpa only [heq] using hu)
    rcases hs with ⟨_,h0 | h1⟩ | ⟨_,hh⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr hh)
  · intro lam v w hw he hl hv
    obtain ⟨ell,hu⟩ := homogeneous_matched_contour_jordan_mode_fixed n z hX hz N
      ha ha1 hk q hq P hcomm hfin G hG lam v w hw he hv
    exact hj z hX hz ell lam hl hu

end DefocusingNLS

end OAI
