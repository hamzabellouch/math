import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralCoercivity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureBoundary

namespace OAI

/-! The upper-half-plane coercivity estimate with a controlled boundary trace. -/

open Set Filter
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialScalarForm_coercive_boundary (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R σ K H : ℝ) (hR : 0 ≤ R) (hσ : 4 ≤ σ)
    (q dq f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hq : ∀ r ∈ Icc 0 R, 0 ≤ q r)
    (hw : ∀ r ∈ Icc 0 R, 0 ≤ deriv (radialMatchedVelocity n z) r)
    (hsmall : 2*(∫ r in (0 : ℝ)..R, radialMassFlux n z r*dq r*(f r)^2) ≤
      radialScalarForm n z R q f f+K*H) :
    (3/4 : ℝ)*radialScalarForm n z R q f f ≤
      σ*radialScalarForm n z R q f f+radialScalarVirial n z R q dq f+(K/4)*H := by
  have hD := radialDrift_integral_lower n z hX hz R hR f hf hw
  have hE := radialScalarForm_nonneg n z R hR q f hq
  have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  have hcoef : 1 ≤ σ-(6-2*radialShootingA n)/2 := by linarith
  have hbound := mul_le_mul_of_nonneg_right hcoef hE
  rw [radialScalarForm_diag] at hbound hsmall hE ⊢
  unfold radialScalarVirial
  nlinarith

theorem radialMatched_spectral_coercivity_boundary :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ R σ : ℝ, 0 ≤ R → 4 ≤ σ →
      ∀ f : ℝ → ℝ, ContDiff ℝ 1 f →
      (3/4 : ℝ)*radialScalarForm n z R (radialSpectralPressure n z) f f ≤
        σ*radialScalarForm n z R (radialSpectralPressure n z) f f+
          radialScalarVirial n z R (radialSpectralPressure n z)
            (deriv (radialSpectralPressure n z)) f+
          C*radialHardyFlux (radialShootingA n) R*(f R)^2 := by
  obtain ⟨c,hc,hW⟩ := radialMatched_uniform_deformation
  obtain ⟨K,hK,hP⟩ := radialMatched_pressure_energy_absorption_boundary
  refine ⟨K/4,by positivity,?_⟩
  filter_upwards [hW,hP] with n hwn hpn z hX hz R σ hR hσ f hf
  have hh := radialScalarForm_coercive_boundary n z hX hz R σ K
    (radialHardyFlux (radialShootingA n) R*(f R)^2) hR hσ
    (radialSpectralPressure n z) (deriv (radialSpectralPressure n z)) f hf
  apply (show (3/4 : ℝ)*radialScalarForm n z R (radialSpectralPressure n z) f f ≤
      σ*radialScalarForm n z R (radialSpectralPressure n z) f f+
        radialScalarVirial n z R (radialSpectralPressure n z)
          (deriv (radialSpectralPressure n z)) f+
        (K/4)*(radialHardyFlux (radialShootingA n) R*(f R)^2) from ?_).trans_eq (by ring)
  apply hh
  · intro r _
    have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
    unfold radialSpectralPressure
    positivity
  · intro r hr
    exact hc.le.trans (hwn z hX hz r hr.1).1
  · have h := hpn z hX hz R hR f hf
    dsimp only at h
    rw [radialScalarForm_diag]
    delta radialSpectralPressure
    have he := h.trans_eq (show
      (∫ r in (0 : ℝ)..R, r^11*‖radialMatchedProfile n z r‖^2*
        (‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold))/radialShootingA n)*(f r)^2)+
      (∫ r in (0 : ℝ)..R, r^11*‖radialMatchedProfile n z r‖^2*(deriv f r)^2)+
        K*radialHardyFlux (radialShootingA n) R*(f R)^2=
      (∫ r in (0 : ℝ)..R, r^11*‖radialMatchedProfile n z r‖^2*(deriv f r)^2)+
      (∫ r in (0 : ℝ)..R, r^11*‖radialMatchedProfile n z r‖^2*
        (‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold))/radialShootingA n)*(f r)^2)+
        K*(radialHardyFlux (radialShootingA n) R*(f R)^2) by ring)
    simpa only [radialMassDensity,radialMassFlux,mul_assoc] using he

end DefocusingNLS

end OAI
