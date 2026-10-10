import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralTesting
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureAbsorption

namespace OAI

/-! Coercivity of the exact upper-half-plane energy form. -/

open Set Filter
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialScalarForm_diag (n : ℕ) (z : ProfileMatchingBall)
    (R : ℝ) (q f : ℝ → ℝ) :
    radialScalarForm n z R q f f=
      (∫ r in (0 : ℝ)..R, radialMassDensity n z r*(deriv f r)^2)+
      ∫ r in (0 : ℝ)..R, radialMassDensity n z r*q r*(f r)^2 := by
  unfold radialScalarForm
  congr 1 <;> apply intervalIntegral.integral_congr <;> intro r _ <;> ring

theorem radialScalarForm_nonneg (n : ℕ) (z : ProfileMatchingBall)
    (R : ℝ) (hR : 0 ≤ R) (q f : ℝ → ℝ) (hq : ∀ r ∈ Icc 0 R, 0 ≤ q r) :
    0 ≤ radialScalarForm n z R q f f := by
  rw [radialScalarForm_diag]
  apply add_nonneg
  · apply intervalIntegral.integral_nonneg hR
    intro r hr
    have hr0 := hr.1
    unfold radialMassDensity
    positivity
  · apply intervalIntegral.integral_nonneg hR
    intro r hr
    have hr0 := hr.1
    have hqr := hq r hr
    unfold radialMassDensity
    positivity

theorem radialDrift_integral_lower (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 ≤ R) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f)
    (hw : ∀ r ∈ Icc 0 R, 0 ≤ deriv (radialMatchedVelocity n z) r) :
    -((6-2*radialShootingA n)/2)*(∫ r in (0 : ℝ)..R, radialMassDensity n z r*(deriv f r)^2) ≤
      ∫ r in (0 : ℝ)..R, radialDriftDensity n z r*(deriv f r)^2 := by
  have hG := ((radialMassDensity_continuous n z hX hz).mul
    (hf.continuous_deriv_one.pow 2)).intervalIntegrable (μ := MeasureTheory.volume) 0 R
  have hD := ((radialDriftDensity_continuousOn n z hX hz R).mul
    (hf.continuous_deriv_one.pow 2).continuousOn).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) hR
  have hpoint : ∀ r ∈ Icc 0 R,
      -((6-2*radialShootingA n)/2)*(radialMassDensity n z r*(deriv f r)^2) ≤
        radialDriftDensity n z r*(deriv f r)^2 := by
    intro r hr
    rw [radialDriftDensity_eq n z hX hz r hr.1]
    have hM : 0 ≤ radialMassDensity n z r := by
      have hr0 := hr.1
      unfold radialMassDensity
      positivity
    nlinarith [mul_nonneg (mul_nonneg hM (hw r hr)) (sq_nonneg (deriv f r))]
  have hh := intervalIntegral.integral_mono_on hR
    (hG.const_mul (-((6-2*radialShootingA n)/2))) hD hpoint
  simpa only [intervalIntegral.integral_const_mul,Pi.mul_apply,Pi.pow_apply] using hh

theorem radialScalarForm_coercive (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R σ : ℝ) (hR : 0 ≤ R) (hσ : 4 ≤ σ)
    (q dq f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hq : ∀ r ∈ Icc 0 R, 0 ≤ q r)
    (hw : ∀ r ∈ Icc 0 R, 0 ≤ deriv (radialMatchedVelocity n z) r)
    (hsmall : 2*(∫ r in (0 : ℝ)..R, radialMassFlux n z r*dq r*(f r)^2) ≤
      radialScalarForm n z R q f f) :
    (3/4 : ℝ)*radialScalarForm n z R q f f ≤
      σ*radialScalarForm n z R q f f+radialScalarVirial n z R q dq f := by
  have hD := radialDrift_integral_lower n z hX hz R hR f hf hw
  have hE := radialScalarForm_nonneg n z R hR q f hq
  have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  have hcoef : 1 ≤ σ-(6-2*radialShootingA n)/2 := by linarith
  have hbound := mul_le_mul_of_nonneg_right hcoef hE
  rw [radialScalarForm_diag] at hbound hsmall hE ⊢
  unfold radialScalarVirial
  nlinarith

noncomputable def radialSpectralPressure (n : ℕ) (z : ProfileMatchingBall) (r : ℝ) : ℝ :=
  ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold))/radialShootingA n

theorem radialMatched_spectral_coercivity :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ R σ : ℝ, 0 ≤ R → 4 ≤ σ →
      ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → f R=0 →
      (3/4 : ℝ)*radialScalarForm n z R (radialSpectralPressure n z) f f ≤
        σ*radialScalarForm n z R (radialSpectralPressure n z) f f+
          radialScalarVirial n z R (radialSpectralPressure n z)
            (deriv (radialSpectralPressure n z)) f := by
  obtain ⟨c,hc,hW⟩ := radialMatched_uniform_deformation
  filter_upwards [hW,radialMatched_pressure_energy_absorption] with n hwn hpn
    z hX hz R σ hR hσ f hf hfR
  apply radialScalarForm_coercive n z hX hz R σ hR hσ _ _ f hf
  · intro r _
    have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
    unfold radialSpectralPressure
    positivity
  · intro r hr
    exact hc.le.trans (hwn z hX hz r hr.1).1
  · have h := hpn z hX hz R hR f hf hfR
    dsimp only at h
    rw [radialScalarForm_diag]
    delta radialSpectralPressure
    simpa only [radialMassDensity,radialMassFlux,mul_assoc] using h.trans_eq (add_comm _ _)

end DefocusingNLS

end OAI
