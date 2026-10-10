import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMatchedHarmonic
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicBounded

namespace OAI

/-! # Bounded C² data for the nonzero matched radial channel

The faithful physical realization is a C₀ function. The same spherical test
used to obtain a nonzero channel therefore gives a global uniform bound,
alongside the exact radial equation and top-derivative square integrability.
-/

open Set MeasureTheory
open scoped ContDiff

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneous_matched_contour_nonzero_bounded_radial (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (N : ℕ)
    (ha : 0 < radialShootingA n) (ha1 : radialShootingA n < 1) (hk : 8 < (N : ℝ))
    (q : HomogeneousY (radialShootingA n) N)
    (hq : ∀ x : E, homogeneousPhysicalCLM (radialShootingA n) N ha ha1 hk q x =
      radialMatchedCartesian n z x)
    (P : (HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N) →L[ℂ]
      (HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N))
    (hcomm : ∀ t, Commute (homogeneousComplexLinearizedStep (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
      (n + radialInnerShootingThreshold) q t) P)
    (hfin : FiniteDimensional ℂ P.range) (G : P.range →L[ℂ] P.range)
    (hG : ∀ t, projectionSemigroupRestriction
      (homogeneousComplexLinearizedStep (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
        (n + radialInnerShootingThreshold) q) P hcomm t = NormedSpace.exp ((t : ℝ) • G))
    (lam : ℂ) (w : P.range) (hw : w ≠ 0) (he : G w = lam • w) :
    ∃ (ell : ℕ) (f g : ℝ → ℂ),
      ContDiff ℝ 2 f ∧ ContDiff ℝ 2 g ∧
      IsHarmonicRadialEigenpair (radialShootingA n)
        (radialShootingB (profileMatchingParameter z))
        (n + radialInnerShootingThreshold) (radialMatchedProfile n z)
        ((ell : ℂ) * (ell + 10)) lam f g ∧
      ContDiffOn ℝ ∞ f (Ioi 0) ∧ ContDiffOn ℝ ∞ g (Ioi 0) ∧
      IntegrableOn (fun r : ℝ => r ^ 11 * ‖iteratedDeriv N f r‖ ^ 2) (Ioi 0) ∧
      IntegrableOn (fun r : ℝ => r ^ 11 * ‖iteratedDeriv N g r‖ ^ 2) (Ioi 0) ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ, ‖(f r, g r)‖ ≤ M) ∧
      ∃ r : ℝ, 0 < r ∧ (f r ≠ 0 ∨ g r ≠ 0) := by
  let F : E → ℂ := fun x => homogeneousPhysicalCLM (radialShootingA n) N ha ha1 hk
    (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).1 x
  let H : E → ℂ := fun x => homogeneousPhysicalCLM (radialShootingA n) N ha ha1 hk
    (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).2 x
  have hF : Continuous F := (contDiff_homogeneousPhysical _ _ ha ha1 hk _).continuous
  have hH : Continuous H := (contDiff_homogeneousPhysical _ _ ha ha1 hk _).continuous
  have hw0 : (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N) ≠ 0 := by
    intro h
    exact hw (Subtype.ext h)
  have hne : ∃ x : E, F x ≠ 0 ∨ H x ≠ 0 :=
    homogeneous_physical_pair_nonzero _ _ ha ha1 hk w hw0
  obtain ⟨ell, Y, r, hYs, hYr, hYe, hr, hm⟩ :=
    physical_pair_exists_spherical_eigenfunction F H hF hH hne
  obtain ⟨hpair, hfs, hgs, hfl, hgl⟩ := homogeneous_matched_contour_radial
    n z hX hz N ha ha1 hk q hq P hcomm hfin G hG lam w he
    Y ((ell : ℂ) * (ell + 10)) hYs hYr hYe
  have hqr : ∀ x : E, homogeneousPhysicalCLM (radialShootingA n) N ha ha1 hk q x =
      radialMatchedProfile n z ‖x‖ := by
    simpa only [radialMatchedCartesian] using hq
  have hw := projectionSemigroup_eigenvector
    (homogeneousComplexLinearizedStep (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
      (n + radialInnerShootingThreshold) q) P hcomm hfin G hG lam w he
  have hc2 := homogeneous_eigenvector_harmonic_channels
    (radialShootingA n) (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
    (n + radialInnerShootingThreshold) q (radialMatchedProfile n z) hqr w lam hw
    Y ((ell : ℂ) * (ell + 10)) hYs hYr hYe
  obtain ⟨Mf, hMf, hbf⟩ := homogeneous_harmonic_channel_bounded
    (radialShootingA n) N ha ha1 hk
    (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).1 Y hYs
  obtain ⟨Mg, hMg, hbg⟩ := homogeneous_harmonic_channel_bounded
    (radialShootingA n) N ha ha1 hk
    (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).2 Y hYs
  refine ⟨ell, harmonicAngularCoefficient Y F, harmonicAngularCoefficient Y H,
    hc2.1, hc2.2.1, hpair, hfs, hgs, hfl, hgl,
    ⟨max Mf Mg, hMf.trans (le_max_left _ _), ?_⟩, r, hr, hm⟩
  intro s
  rw [Prod.norm_def]
  exact max_le_max (hbf s) (hbg s)

end DefocusingNLS

end OAI
