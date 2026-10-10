import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMatchedBoundedPair

namespace OAI

/-! The exact classical radial data retained from a nonzero contour eigenvector. -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

structure RadialSpectralMode (a b : ℝ) (m N : ℕ) (Q : ℝ → ℂ) (η lam : ℂ) where
  first : ℝ → ℂ
  second : ℝ → ℂ
  first_c2 : ContDiff ℝ 2 first
  second_c2 : ContDiff ℝ 2 second
  equation : IsHarmonicRadialEigenpair a b m Q η lam first second
  first_smooth : ContDiffOn ℝ ∞ first (Ioi 0)
  second_smooth : ContDiffOn ℝ ∞ second (Ioi 0)
  first_top : IntegrableOn (fun r : ℝ => r^11*‖iteratedDeriv N first r‖^2) (Ioi 0)
  second_top : IntegrableOn (fun r : ℝ => r^11*‖iteratedDeriv N second r‖^2) (Ioi 0)
  bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ, ‖(first r,second r)‖ ≤ M
  nonzero : ∃ r : ℝ, 0 < r ∧ (first r ≠ 0 ∨ second r ≠ 0)

theorem homogeneous_matched_contour_radialMode (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (N : ℕ)
    (ha : 0 < radialShootingA n) (ha1 : radialShootingA n < 1) (hk : 8 < (N : ℝ))
    (q : HomogeneousY (radialShootingA n) N)
    (hq : ∀ x : E, homogeneousPhysicalCLM (radialShootingA n) N ha ha1 hk q x=
      radialMatchedCartesian n z x)
    (P : (HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N) →L[ℂ]
      (HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N))
    (hcomm : ∀ t, Commute (homogeneousComplexLinearizedStep (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
      (n+radialInnerShootingThreshold) q t) P)
    (hfin : FiniteDimensional ℂ P.range) (G : P.range →L[ℂ] P.range)
    (hG : ∀ t, projectionSemigroupRestriction
      (homogeneousComplexLinearizedStep (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
        (n+radialInnerShootingThreshold) q) P hcomm t=NormedSpace.exp ((t : ℝ) • G))
    (lam : ℂ) (w : P.range) (hw : w ≠ 0) (he : G w=lam • w) :
    ∃ ell : ℕ, Nonempty (RadialSpectralMode (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold) N
      (radialMatchedProfile n z) ((ell : ℂ)*(ell+10)) lam) := by
  obtain ⟨ell,f,g,hf,hg,hEq,hfs,hgs,hft,hgt,hb,hn⟩ :=
    homogeneous_matched_contour_nonzero_bounded_radial n z hX hz N ha ha1 hk q hq P
      hcomm hfin G hG lam w hw he
  exact ⟨ell,⟨⟨f,g,hf,hg,hEq,hfs,hgs,hft,hgt,hb,hn⟩⟩⟩

end DefocusingNLS

end OAI
