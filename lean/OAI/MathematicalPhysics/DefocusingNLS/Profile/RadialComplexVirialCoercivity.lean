import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexVirial
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShiftedVirialCoercivity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorPressureTransport
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralPressureCalculus

namespace OAI

/-! The actual pressure and deformation estimates give uniform complex
virial coercivity, with only the first-component L2 mass as an error. -/

open Set Filter MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem radialComplexShiftedVirial_coercive (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (eta R k C : ℝ) (heta : 0 ≤ eta) (hR : 0 ≤ R)
    (q dq : ℝ → ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hdq : ContinuousOn dq (Icc 0 R))
    (hvel : ∀ r ∈ Icc 0 R, k ≤ deriv (radialMatchedVelocity n z) r ∧
      k ≤ radialMatchedVelocityRatio n z r)
    (hp : ∀ r ∈ Icc 0 R, radialMatchedVelocity n z r*dq r ≤ C) :
    k*radialComplexAngularForm n z eta R (fun _ => 0) f ≤
      ((6-2*radialShootingA n)/2)*radialComplexAngularForm n z eta R q f+
        radialComplexAngularVirial n z eta R q dq f+
        (C/2)*(∫ r in (0 : ℝ)..R, radialMassDensity n z r*‖f r‖^2) := by
  have hfr : ContDiff ℝ 1 (fun r => (f r).re) := Complex.reCLM.contDiff.comp hf
  have hfi : ContDiff ℝ 1 (fun r => (f r).im) := Complex.imCLM.contDiff.comp hf
  have hr := radialShiftedVirial_coercive n z hX hz eta R k C heta hR q dq
    (fun r => (f r).re) hfr hdq hvel hp
  have hi := radialShiftedVirial_coercive n z hX hz eta R k C heta hR q dq
    (fun r => (f r).im) hfi hdq hvel hp
  have hM := radialMassDensity_continuous n z hX hz
  have hsum : (∫ r in (0 : ℝ)..R, radialMassDensity n z r*(f r).re^2)+
      (∫ r in (0 : ℝ)..R, radialMassDensity n z r*(f r).im^2) =
      ∫ r in (0 : ℝ)..R, radialMassDensity n z r*‖f r‖^2 := by
    have hri : IntervalIntegrable (fun r => radialMassDensity n z r*(f r).re^2) volume 0 R :=
      (hM.mul (hfr.continuous.pow 2)).intervalIntegrable 0 R
    have hii : IntervalIntegrable (fun r => radialMassDensity n z r*(f r).im^2) volume 0 R :=
      (hM.mul (hfi.continuous.pow 2)).intervalIntegrable 0 R
    rw [← intervalIntegral.integral_add hri hii]
    apply intervalIntegral.integral_congr
    intro r _
    simp only [Complex.sq_norm,Complex.normSq_apply]
    ring
  have heq := congrArg (fun x : ℝ => (C/2)*x) hsum
  dsimp only [radialComplexAngularForm,radialComplexAngularVirial]
  nlinarith only [hr,hi,heq]

theorem radialMatched_complex_virial_coercive :
    ∃ k : ℝ, 0 < k ∧ ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ eta R : ℝ, 0 ≤ eta → 0 ≤ R →
      ∀ f : ℝ → ℂ, ContDiff ℝ 1 f →
      k*radialComplexAngularForm n z eta R (fun _ => 0) f ≤
        ((6-2*radialShootingA n)/2)*radialComplexAngularForm n z eta R (radialSpectralPressure n z) f+
        radialComplexAngularVirial n z eta R (radialSpectralPressure n z) (deriv (radialSpectralPressure n z)) f+
        800*(∫ r in (0 : ℝ)..R, radialMassDensity n z r*‖f r‖^2) := by
  obtain ⟨k,hk,hdef⟩ := radialMatched_uniform_deformation
  refine ⟨k,hk,?_⟩
  filter_upwards [hdef,radialMatched_global_pressure_transport_bound] with n hn hp
  intro z hX hz eta R heta hR f hf
  have hdq := radialSpectralPressure_deriv_continuousOn n z hX hz R
  have hvel r (hr : r ∈ Icc 0 R) : k ≤ deriv (radialMatchedVelocity n z) r ∧
      k ≤ radialMatchedVelocityRatio n z r := hn z hX hz r hr.1
  have hpress r (hr : r ∈ Icc 0 R) :
      radialMatchedVelocity n z r*deriv (radialSpectralPressure n z) r ≤ 1600 := hp z hX hz r hr.1
  have hfr : ContDiff ℝ 1 (fun r => (f r).re) := Complex.reCLM.contDiff.comp hf
  have hfi : ContDiff ℝ 1 (fun r => (f r).im) := Complex.imCLM.contDiff.comp hf
  have hr := radialShiftedVirial_coercive n z hX hz eta R k 1600 heta hR
    (radialSpectralPressure n z) (deriv (radialSpectralPressure n z)) (fun r => (f r).re) hfr hdq hvel hpress
  have hi := radialShiftedVirial_coercive n z hX hz eta R k 1600 heta hR
    (radialSpectralPressure n z) (deriv (radialSpectralPressure n z)) (fun r => (f r).im) hfi hdq hvel hpress
  have hM := radialMassDensity_continuous n z hX hz
  have hsum : (∫ r in (0 : ℝ)..R, radialMassDensity n z r*(f r).re^2)+
      (∫ r in (0 : ℝ)..R, radialMassDensity n z r*(f r).im^2) =
      ∫ r in (0 : ℝ)..R, radialMassDensity n z r*‖f r‖^2 := by
    have hri : IntervalIntegrable (fun r => radialMassDensity n z r*(f r).re^2) volume 0 R :=
      (hM.mul (hfr.continuous.pow 2)).intervalIntegrable 0 R
    have hii : IntervalIntegrable (fun r => radialMassDensity n z r*(f r).im^2) volume 0 R :=
      (hM.mul (hfi.continuous.pow 2)).intervalIntegrable 0 R
    rw [← intervalIntegral.integral_add hri hii]
    apply intervalIntegral.integral_congr
    intro r _
    simp only [Complex.sq_norm,Complex.normSq_apply]
    ring
  dsimp only [radialComplexAngularForm,radialComplexAngularVirial]
  norm_num only [show (1600 : ℝ)/2=800 by norm_num] at hr hi
  nlinarith only [hr,hi,hsum]

end DefocusingNLS

end OAI
