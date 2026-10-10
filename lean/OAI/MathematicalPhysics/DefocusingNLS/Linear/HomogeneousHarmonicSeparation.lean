import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicTrace
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicFunctional

namespace OAI

/-! # A scalar trace of the allowed angular degree separates a contour eigenspace -/

open Set MeasureTheory
open scoped ContDiff Laplacian
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneous_contour_harmonic_trace_separates (n : ℕ) (z : ProfileMatchingBall)
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
    (ell₀ : ℕ)
    (hclass : ∀ (ell : ℕ), Nonempty (RadialSpectralMode (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold) 9
      (radialMatchedProfile n z) ((ell : ℂ) * (ell + 10)) lam) → ell = ell₀)
    (hline : RadialModeLine n z ell₀ 9 lam)
    (u₀ : RadialSpectralMode (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold) 9
      (radialMatchedProfile n z) ((ell₀ : ℂ) * (ell₀ + 10)) lam)
    (first : Bool) (r₀ : ℝ) (hr₀ : 0 < r₀) (hu₀ : radialModeTrace u₀ first r₀ ≠ 0)
    (htrace : ∀ (p : PhysicalRealPolynomial), p.IsHomogeneous ell₀ →
      physicalPolynomialLaplacian p = 0 →
      homogeneousPairHarmonicMoment (radialShootingA n) N ha ha1 hk
        (physicalHarmonicExtension p ell₀)
        (continuous_harmonicSphere _ (physicalHarmonicExtension_contDiffAt p ell₀)) first r₀ w = 0) :
    w = 0 := by
  let F : E → ℂ := fun x => homogeneousPhysicalCLM (radialShootingA n) N ha ha1 hk
    (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).1 x
  let H : E → ℂ := fun x => homogeneousPhysicalCLM (radialShootingA n) N ha ha1 hk
    (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).2 x
  have hall (p : PhysicalRealPolynomial) (ell : ℕ) (hp : p.IsHomogeneous ell)
      (hDp : physicalPolynomialLaplacian p = 0) :
      ∀ r : ℝ, 0 < r →
        harmonicAngularCoefficient (physicalHarmonicExtension p ell) F r = 0 ∧
        harmonicAngularCoefficient (physicalHarmonicExtension p ell) H r = 0 := by
    apply homogeneous_contour_harmonic_zero_of_exclusion n z hX hz N ha ha1 hk q hq
      P hcomm hfin G hG lam w he ell (physicalHarmonicExtension p ell)
      (physicalHarmonicExtension_contDiffAt p ell)
      (physicalHarmonicExtension_ray p ell hp)
      (physicalHarmonicExtension_laplacian p ell hp hDp)
    intro u hu hv
    have hel := hclass ell ⟨u⟩
    subst ell
    have ht := htrace p hp hDp
    have hne := hline.trace_ne_zero u₀ u first r₀ hr₀ hu₀
    apply hne
    cases first
    · change u.second r₀ = 0
      rw [hv]
      exact ht
    · change u.first r₀ = 0
      rw [hu]
      exact ht
  have hF : F = 0 := physical_zero_of_harmonic_coefficients F
    (homogeneousPhysicalCLM (radialShootingA n) N ha ha1 hk _).continuous
    (fun p ell hp hd r hr => (hall p ell hp hd r hr).1)
  have hH : H = 0 := physical_zero_of_harmonic_coefficients H
    (homogeneousPhysicalCLM (radialShootingA n) N ha ha1 hk _).continuous
    (fun p ell hp hd r hr => (hall p ell hp hd r hr).2)
  by_contra hw
  have hne := homogeneous_physical_pair_nonzero (radialShootingA n) N ha ha1 hk
    (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N)
    (fun h => hw (Subtype.ext h))
  obtain ⟨x, hx | hx⟩ := hne
  · exact hx (congrFun hF x)
  · exact hx (congrFun hH x)

end DefocusingNLS

end OAI
