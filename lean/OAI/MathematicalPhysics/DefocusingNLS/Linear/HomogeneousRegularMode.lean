import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRegularCompleteness
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralMode
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedEvenProfile
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhysicalScaling

namespace OAI

/-! The actual classical harmonic mode supplies the regular-basis data. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem homogeneous_matched_mode_state (n N : ℕ) (z : ProfileMatchingBall)
    (eta lam : ℂ)
    (u : RadialSpectralMode (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold) N
      (radialMatchedProfile n z) eta lam) :
    ContDiff ℝ 2 (fun r => (harmonicRadialState u.first u.second r).1.1) ∧
    ContDiff ℝ 2 (fun r => (harmonicRadialState u.first u.second r).2.1) ∧
    ∀ r, 0 < r → HasDerivAt (harmonicRadialState u.first u.second)
      (spectralPhysicalCircularField
        (radialShootingNu (n + radialInnerShootingThreshold) z - 2 * lam)
        (star (radialShootingNu (n + radialInnerShootingThreshold) z) - 2 * lam)
        eta (n + radialInnerShootingThreshold) (radialMatchedEvenProfile n z r) r
        (harmonicRadialState u.first u.second r)) r := by
  refine ⟨u.first_c2, u.second_c2, ?_⟩
  intro r hr
  have hs : star (radialShootingNu (n + radialInnerShootingThreshold) z) =
      -2 * (radialShootingA n : ℂ) -
        2 * Complex.I * (radialShootingB (profileMatchingParameter z) : ℂ) := by
    rw [radialShootingNu_physical]
    simp only [star_add, star_mul, star_neg, star_ofNat, Complex.star_def,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hs, radialShootingNu_physical, radialMatchedEvenProfile_nonneg n z r hr.le]
  exact harmonicRadialState_hasDerivAt (radialShootingA n)
    (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold)
    (radialMatchedProfile n z) u.first u.second eta lam u.first_c2 u.second_c2 u.equation r hr

theorem homogeneous_matched_mode_state_ne_zero (n N : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (eta lam : ℂ)
    (u : RadialSpectralMode (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold) N
      (radialMatchedProfile n z) eta lam) (R : ℝ) (hR : 0 < R) :
    harmonicRadialState u.first u.second R ≠ 0 := by
  intro hzero
  obtain ⟨r, hr, hn⟩ := u.nonzero
  have he := harmonicRadialState_zero_of_zero (radialShootingA n)
    (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold)
    (radialMatchedProfile n z) u.first u.second eta lam
    (radialMatchedProfile_differentiable n z hX hz).continuous.continuousOn
    u.first_c2 u.second_c2 u.equation R hR hzero r hr
  rcases hn with hf | hg
  · exact hf (congrArg (fun w : E₄ => w.1.1) he)
  · exact hg (congrArg (fun w : E₄ => w.2.1) he)

theorem homogeneous_matched_mode_regular_span (n N : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (eta : ℝ) (heta : 0 ≤ eta) (lam : ℂ)
    (u : RadialSpectralMode (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold) N
      (radialMatchedProfile n z) (eta : ℂ) lam) (R : ℝ) (hR : 0 < R)
    (Rp Rm : ℝ → E₄)
    (hpc : ContDiff ℝ 2 (fun r => (Rp r).1.1) ∧ ContDiff ℝ 2 (fun r => (Rp r).2.1))
    (hmc : ContDiff ℝ 2 (fun r => (Rm r).1.1) ∧ ContDiff ℝ 2 (fun r => (Rm r).2.1))
    (hp : ∀ r ∈ Ioc 0 R, HasDerivAt Rp
      (spectralPhysicalCircularField
        (radialShootingNu (n + radialInnerShootingThreshold) z - 2 * lam)
        (star (radialShootingNu (n + radialInnerShootingThreshold) z) - 2 * lam)
        (eta : ℂ) (n + radialInnerShootingThreshold) (radialMatchedEvenProfile n z r) r (Rp r)) r)
    (hm : ∀ r ∈ Ioc 0 R, HasDerivAt Rm
      (spectralPhysicalCircularField
        (radialShootingNu (n + radialInnerShootingThreshold) z - 2 * lam)
        (star (radialShootingNu (n + radialInnerShootingThreshold) z) - 2 * lam)
        (eta : ℂ) (n + radialInnerShootingThreshold) (radialMatchedEvenProfile n z r) r (Rm r)) r)
    (hrank : LinearIndependent ℂ ![Rp R, Rm R]) :
    ∃ c : ℂ × ℂ, harmonicRadialState u.first u.second R = c.1 • Rp R + c.2 • Rm R := by
  obtain ⟨huc1, huc2, hu⟩ := homogeneous_matched_mode_state n N z (eta : ℂ) lam u
  exact homogeneousRegular_basis_complete
    (radialShootingNu (n + radialInnerShootingThreshold) z - 2 * lam)
    (star (radialShootingNu (n + radialInnerShootingThreshold) z) - 2 * lam)
    eta heta (n + radialInnerShootingThreshold) (radialMatchedEvenProfile n z)
    (radialMatchedEvenProfile_contDiff n z hX hz).continuous R hR
    (harmonicRadialState u.first u.second) Rp Rm ⟨huc1, huc2⟩ hpc hmc
    (fun r hr => hu r hr.1) hp hm hrank

end DefocusingNLS

end OAI
