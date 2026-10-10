import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMatchedBoundedPair
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicPairEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialJordanSmoothness
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialJordanMode

namespace OAI

/-! Every nontrivial finite-dimensional generator Jordan pair yields an actual finite-energy radial pair. -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneous_matched_contour_jordan_mode (n : ℕ) (z : ProfileMatchingBall)
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
    (lam : ℂ) (v w : P.range) (hw : w ≠ 0) (he : G w = lam • w)
    (hJordan : G v=lam • v+w) :
    ∃ ell : ℕ, HasRadialJordanMode n z ell N lam := by
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
  let A := fun f : HomogeneousY (radialShootingA n) N =>
    harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM (radialShootingA n) N ha ha1 hk f x)
  have hwb := homogeneous_harmonic_pair_bounded (radialShootingA n) N ha ha1 hk
    (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N) Y hYs
  let u : RadialSpectralMode (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) N (radialMatchedProfile n z) ((ell : ℂ)*(ell+10)) lam :=
    ⟨A (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).1,
      A (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).2,
      hc2.1,hc2.2.1,hpair,hfs,hgs,hfl,hgl,hwb,⟨r,hr,hm⟩⟩
  obtain ⟨hv₁,hv₂,hve⟩ := homogeneous_contour_jordan_radial (radialShootingA n)
    (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
    (n+radialInnerShootingThreshold) q (radialMatchedProfile n z) hqr P hcomm hfin G hG
    lam v w hJordan Y ((ell : ℂ)*(ell+10)) hYs hYr hYe
  have hvs := harmonicRadialSourcePair_contDiffOn (radialShootingA n)
    (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
    (radialMatchedProfile n z)
    (A (v : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).1)
    (A (v : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).2)
    u.first u.second ((ell : ℂ)*(ell+10)) lam hv₁ hv₂ hve 0 le_rfl
    (radialMatchedProfile_contDiffOn n z hX hz) hfs hgs
  have hvt := homogeneous_harmonic_pair_topL2 (radialShootingA n) N ha ha1 hk
    (v : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N) Y hYs hvs.1 hvs.2
  have hvb := homogeneous_harmonic_pair_bounded (radialShootingA n) N ha ha1 hk
    (v : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N) Y hYs
  exact ⟨ell,u,_,_,hv₁,hv₂,hve,hvt.1,hvt.2,hvb⟩

end DefocusingNLS

end OAI
