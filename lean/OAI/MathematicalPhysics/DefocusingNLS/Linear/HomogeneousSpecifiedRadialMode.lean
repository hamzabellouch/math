import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFixedRadialModes

namespace OAI

/-! # The finite-energy radial mode in any specified nonzero harmonic channel -/

open Set MeasureTheory
open scoped ContDiff Laplacian
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneous_matched_contour_specified_radialMode (n : ℕ) (z : ProfileMatchingBall)
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
    (hne : ∃ r : ℝ, 0 < r ∧
      (harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM (radialShootingA n) N ha ha1 hk
        (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).1 x) r ≠ 0 ∨
      harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM (radialShootingA n) N ha ha1 hk
        (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).2 x) r ≠ 0)) :
    ∃ u : RadialSpectralMode (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold) 9
      (radialMatchedProfile n z) ((ell : ℂ) * (ell + 10)) lam,
      u.first = harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM (radialShootingA n) N
        ha ha1 hk (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).1 x) ∧
      u.second = harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM (radialShootingA n) N
        ha ha1 hk (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).2 x) := by
  obtain ⟨r, hr, hm⟩ := hne
  obtain ⟨hpair, hfs, hgs, _, _⟩ := homogeneous_matched_contour_radial
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
  have hN9 : 9 ≤ N := by
    have hh : 8 < N := by exact_mod_cast hk
    omega
  have htop := homogeneous_harmonic_pair_lower_topL2 (radialShootingA n) N 9 ha ha1 hk
    (by norm_num) hN9 (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N)
    Y hYs hfs hgs
  let u : RadialSpectralMode (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) 9 (radialMatchedProfile n z) ((ell : ℂ)*(ell+10)) lam :=
    ⟨A (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).1,
      A (w : HomogeneousY (radialShootingA n) N × HomogeneousY (radialShootingA n) N).2,
      hc2.1,hc2.2.1,hpair,hfs,hgs,htop.1,htop.2,hwb,⟨r,hr,hm⟩⟩
  exact ⟨u, rfl, rfl⟩

end DefocusingNLS

end OAI
