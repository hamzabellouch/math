import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCartesianSmooth

namespace OAI

/-! A smooth nonvanishing extension of the actual profile to signed radii. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def radialMatchedEvenProfile (n : ℕ) (z : ProfileMatchingBall) (r : ℝ) : ℂ :=
  radialMatchedCartesian n z (r • (EuclideanSpace.basisFun (Fin 12) ℝ) 0)

theorem radialMatchedEvenProfile_eq (n : ℕ) (z : ProfileMatchingBall) (r : ℝ) :
    radialMatchedEvenProfile n z r=radialMatchedProfile n z |r| := by
  simp only [radialMatchedEvenProfile,radialMatchedCartesian,norm_smul,Real.norm_eq_abs,
    (EuclideanSpace.basisFun (Fin 12) ℝ).norm_eq_one,mul_one]

theorem radialMatchedEvenProfile_nonneg (n : ℕ) (z : ProfileMatchingBall) (r : ℝ) (hr : 0 ≤ r) :
    radialMatchedEvenProfile n z r=radialMatchedProfile n z r := by
  rw [radialMatchedEvenProfile_eq,abs_of_nonneg hr]

theorem radialMatchedEvenProfile_contDiff (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) : ContDiff ℝ ∞ (radialMatchedEvenProfile n z) :=
  (radialMatchedCartesian_contDiff n z hX hz).comp (contDiff_id.smul contDiff_const)

theorem radialMatchedEvenProfile_ne_zero (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (r : ℝ) : radialMatchedEvenProfile n z r ≠ 0 := by
  rw [radialMatchedEvenProfile_eq]
  exact radialMatchedProfile_ne_zero n z hX |r| (abs_nonneg r)

theorem radialMatchedEvenProfile_eventuallyEq (n : ℕ) (z : ProfileMatchingBall)
    (r : ℝ) (hr : 0 < r) :
    radialMatchedEvenProfile n z =ᶠ[𝓝 r] radialMatchedProfile n z := by
  filter_upwards [Ioi_mem_nhds hr] with t ht
  exact radialMatchedEvenProfile_nonneg n z t ht.le

theorem radialMatchedEvenProfile_stationary (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : 0 < r) :
    let Q := radialMatchedEvenProfile n z
    Complex.I*(deriv (deriv Q) r+11/(r : ℂ)*deriv Q r)-
      (r : ℂ)/2*deriv Q r+
      (-(radialShootingA n : ℂ)+Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ))*Q r-
      Complex.I*((‖Q r‖^(2*(n+radialInnerShootingThreshold)) : ℝ) : ℂ)*Q r=0 := by
  dsimp only
  have he := radialMatchedEvenProfile_eventuallyEq n z r hr
  have h := radialMatchedProfile_stationary n z hX hz r hr
  rw [← he.eq_of_nhds,← he.deriv_eq,← he.deriv.deriv_eq,oddPowerNonlinearity_eq] at h
  push_cast at h ⊢
  linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring)) Complex.I*h

end DefocusingNLS

end OAI
