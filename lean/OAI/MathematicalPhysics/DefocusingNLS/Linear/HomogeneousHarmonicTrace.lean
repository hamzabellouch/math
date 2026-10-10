import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpecifiedRadialMode
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialModeTrace

namespace OAI

/-! # Vanishing of a specified harmonic channel from radial exclusion -/

open Set MeasureTheory
open scoped ContDiff Laplacian
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneous_contour_harmonic_zero_of_exclusion (n : ℕ) (z : ProfileMatchingBall)
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
    (ell : ℕ) (Y : E → ℂ)
    (hYs : ∀ x : E, x ≠ 0 → ContDiffAt ℝ ∞ Y x)
    (hYr : ∀ (x : E) (t : ℝ), 0 < t → Y (t • x) = Y x)
    (hYe : ∀ x : E, x ≠ 0 → Δ Y x = -(((ell : ℂ) * (ell + 10)) / (‖x‖ ^ 2 : ℝ)) * Y x)
    (hreject : ∀ u : RadialSpectralMode (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold) 9
      (radialMatchedProfile n z) ((ell : ℂ) * (ell + 10)) lam,
      u.first = harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM (radialShootingA n) N
        ha ha1 hk (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).1 x) →
      u.second = harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM (radialShootingA n) N
        ha ha1 hk (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).2 x) → False) :
    ∀ r : ℝ, 0 < r →
      harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM (radialShootingA n) N
        ha ha1 hk (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).1 x) r = 0 ∧
      harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM (radialShootingA n) N
        ha ha1 hk (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).2 x) r = 0 := by
  intro r hr
  by_contra hzero
  have hne : harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM (radialShootingA n) N
      ha ha1 hk (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).1 x) r ≠ 0 ∨
      harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM (radialShootingA n) N
      ha ha1 hk (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).2 x) r ≠ 0 := by
    tauto
  obtain ⟨u, hu, hv⟩ := homogeneous_matched_contour_specified_radialMode n z hX hz N ha ha1 hk q hq
    P hcomm hfin G hG lam w he ell Y hYs hYr hYe ⟨r, hr, hne⟩
  exact hreject u hu hv

end DefocusingNLS

end OAI
