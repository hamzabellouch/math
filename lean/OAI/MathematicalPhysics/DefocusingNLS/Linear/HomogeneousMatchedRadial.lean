import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicEigenL2
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousContourGenerator
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedSymbol

namespace OAI

/-! # Radial channels of the actual matched-profile contour generator

The profile is the already constructed matched stationary solution. Its
smoothness supplies the exterior hypothesis of the radial L² theorem.
-/

open Set MeasureTheory
open scoped ContDiff Laplacian

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneous_matched_contour_radial (n : ℕ) (z : ProfileMatchingBall)
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
    (lam : ℂ) (w : P.range) (he : G w = lam • w)
    (Y : E → ℂ) (eta : ℂ)
    (hY : ∀ x : E, x ≠ 0 → ContDiffAt ℝ ∞ Y x)
    (hRay : ∀ (x : E) (t : ℝ), 0 < t → Y (t • x) = Y x)
    (hEigen : ∀ x : E, x ≠ 0 → Δ Y x = -(eta / (‖x‖ ^ 2 : ℝ)) * Y x) :
    let f := harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM
      (radialShootingA n) N ha ha1 hk (w : HomogeneousY (radialShootingA n) N ×
        HomogeneousY (radialShootingA n) N).1 x)
    let g := harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM
      (radialShootingA n) N ha ha1 hk (w : HomogeneousY (radialShootingA n) N ×
        HomogeneousY (radialShootingA n) N).2 x)
    IsHarmonicRadialEigenpair (radialShootingA n) (radialShootingB (profileMatchingParameter z))
        (n + radialInnerShootingThreshold) (radialMatchedProfile n z) eta lam f g ∧
      ContDiffOn ℝ ∞ f (Ioi 0) ∧ ContDiffOn ℝ ∞ g (Ioi 0) ∧
      IntegrableOn (fun r : ℝ => r ^ 11 * ‖iteratedDeriv N f r‖ ^ 2) (Ioi 0) ∧
      IntegrableOn (fun r : ℝ => r ^ 11 * ‖iteratedDeriv N g r‖ ^ 2) (Ioi 0) := by
  have hqr : ∀ x : E, homogeneousPhysicalCLM (radialShootingA n) N ha ha1 hk q x =
      radialMatchedProfile n z ‖x‖ := by
    simpa only [radialMatchedCartesian] using hq
  have hw := projectionSemigroup_eigenvector
    (homogeneousComplexLinearizedStep (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
      (n + radialInnerShootingThreshold) q) P hcomm hfin G hG lam w he
  have heq := (homogeneous_eigenvector_harmonic_channels
    (radialShootingA n) (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
    (n + radialInnerShootingThreshold) q (radialMatchedProfile n z) hqr w lam hw
    Y eta hY hRay hEigen).2.2
  exact ⟨heq, homogeneous_eigenvector_harmonic_topL2
    (radialShootingA n) (radialShootingB (profileMatchingParameter z)) N ha ha1 hk
    (n + radialInnerShootingThreshold) q (radialMatchedProfile n z) hqr w lam hw
    Y eta hY hRay hEigen 0 le_rfl (radialMatchedProfile_contDiffOn n z hX hz)⟩

end DefocusingNLS

end OAI
