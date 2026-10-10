import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalParameterL2
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSymmetryIndependence

namespace OAI

/-! The actual outgoing parameter derivative has finite top energy in the counting half-plane. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialCanonicalParameter_top_integrable (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (eta : ℂ) (c : ℂ × ℂ) (Y : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) c Y)
    (lam : ℂ) (hhalf : -(1/32 : ℝ)≤lam.re) (N : ℕ) (hN : 7≤N) :
    ∃ T : ℝ, 1<T ∧ IntegrableOn
      (fun r => r^11*‖iteratedDeriv N
        (canonicalPhysicalParameterValues (radialShootingNu (n+radialInnerShootingThreshold) z) Y lam) r‖^2)
      (Ioi T) := by
  have ha := radialShootingA_positive n z
  have hν : (radialShootingNu (n+radialInnerShootingThreshold) z).re =
      -2*radialShootingA n := by
    rw [radialShootingNu_physical]
    simp only [Complex.add_re,Complex.mul_re,Complex.neg_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,Complex.I_re,Complex.I_im]
    ring
  have hNr : (7 : ℝ)≤N := by exact_mod_cast hN
  have hexp : 11+2*((radialShootingNu (n+radialInnerShootingThreshold) z).re-
      2*lam.re+1/4-(N : ℝ)) < -1 := by rw [hν]; linarith
  exact canonicalPhysicalParameterValues_top_integrable _ eta _ _
    (by have h := radialShootingInner_power_pos n (profileMatchingParameter z); omega)
    _ hX (radialShootingM_ne_zero z) c Y hY lam (1/4) (by norm_num) N hexp

theorem radialCanonicalParameter_eventually_bounded (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (eta : ℂ) (c : ℂ × ℂ) (Y : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) c Y)
    (lam : ℂ) (hlam : 0≤lam.re) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ r in atTop,
      ‖canonicalPhysicalParameterValues (radialShootingNu (n+radialInnerShootingThreshold) z) Y lam r‖≤C := by
  have ha := radialShootingA_positive n z
  have hν : (radialShootingNu (n+radialInnerShootingThreshold) z).re =
      -2*radialShootingA n := by
    rw [radialShootingNu_physical]
    simp only [Complex.add_re,Complex.mul_re,Complex.neg_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,Complex.I_re,Complex.I_im]
    ring
  obtain ⟨C,hC,hbound⟩ := canonicalPhysicalParameterValues_derivative_bound _ eta _ _
    (by have h := radialShootingInner_power_pos n (profileMatchingParameter z); omega)
    _ hX (radialShootingM_ne_zero z) c Y hY lam (radialShootingA n) ha 0
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1 : ℝ)] with r hr hr₁
  simp only [iteratedDeriv_zero,Nat.cast_zero,sub_zero,hν] at hr
  exact hr.trans (mul_le_of_le_one_right hC
    (Real.rpow_le_one_of_one_le_of_nonpos hr₁ (by linarith)))

end DefocusingNLS

end OAI
