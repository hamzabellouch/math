import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexScalarAction
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedGaugeFlux
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralPressureCalculus

namespace OAI

/-! Actual gauge eigenmodes satisfy the regular complex scalar equations,
with the exact mass density and transport field used by the virial form. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_complex_flux_eq (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (f g : ℝ → ℂ) (r : ℝ) (hr : 0 ≤ r) :
    spectralGaugeFirstFlux (radialMatchedMassFunction n z) (radialMatchedTransportFunction n z) f g r =
      (radialMassDensity n z r : ℂ)*deriv f r-(radialMassFlux n z r : ℂ)*g r ∧
    spectralGaugeSecondFlux (radialMatchedMassFunction n z) (radialMatchedTransportFunction n z) f g r =
      (radialMassDensity n z r : ℂ)*deriv g r+(radialMassFlux n z r : ℂ)*f r := by
  have hm : r^11*radialMatchedTransportFunction n z r=radialMassFlux n z r := by
    rw [radialMassFlux_eq n z hX hz r hr]
    congr 1
    exact (radialMatchedWeightedFlux_average_nonneg n z hX hz r hr).symm
  have hmc := congrArg (fun x : ℝ => (x : ℂ)) hm
  push_cast at hmc
  constructor
  · dsimp only [spectralGaugeFirstFlux,radialMassDensity,radialMatchedMassFunction]
    push_cast
    rw [← hmc]
    ring
  · dsimp only [spectralGaugeSecondFlux,radialMassDensity,radialMatchedMassFunction]
    push_cast
    rw [← hmc]
    ring

theorem radialMatched_complex_action (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (eta : ℝ) (lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsRadialLogGaugeEigenpair (n+radialInnerShootingThreshold)
      (radialMatchedEvenProfile n z) (eta : ℂ) lam f g) (r : ℝ) (hr : 0 < r) :
    radialComplexAngularAction n z eta (radialSpectralPressure n z) f r =
      -(radialMassDensity n z r : ℂ)*(lam*g r+(radialMatchedVelocity n z r : ℂ)*deriv g r) ∧
    radialComplexAngularAction n z eta (fun _ => 0) g r =
      (radialMassDensity n z r : ℂ)*(lam*f r+(radialMatchedVelocity n z r : ℂ)*deriv f r) := by
  have hm := (radialMassDensity_hasDerivAt n z hX hz r).ofReal_comp
  have hw := (radialMassFlux_hasDerivAt n z hX hz r hr).ofReal_comp
  have hdf : DifferentiableAt ℝ (deriv f) r := (hf.deriv' (n := 1)).differentiable (by norm_num) r
  have hdg : DifferentiableAt ℝ (deriv g) r := (hg.deriv' (n := 1)).differentiable (by norm_num) r
  have hF := (hm.mul hdf.hasDerivAt).sub (hw.mul (hg.differentiable (by norm_num) r).hasDerivAt)
  have hG := (hm.mul hdg.hasDerivAt).add (hw.mul (hf.differentiable (by norm_num) r).hasDerivAt)
  have heqF : spectralGaugeFirstFlux (radialMatchedMassFunction n z) (radialMatchedTransportFunction n z) f g
      =ᶠ[𝓝 r] (fun t => (radialMassDensity n z t : ℂ)*deriv f t-(radialMassFlux n z t : ℂ)*g t) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact (radialMatched_complex_flux_eq n z hX hz f g t ht.le).1
  have heqG : spectralGaugeSecondFlux (radialMatchedMassFunction n z) (radialMatchedTransportFunction n z) f g
      =ᶠ[𝓝 r] (fun t => (radialMassDensity n z t : ℂ)*deriv g t+(radialMassFlux n z t : ℂ)*f t) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact (radialMatched_complex_flux_eq n z hX hz f g t ht.le).2
  obtain ⟨hFs,hGs⟩ := radialMatchedGauge_flux n z hX hz (eta : ℂ) lam f g hf hg he r hr
  have hfirst := (hF.congr_of_eventuallyEq heqF).unique hFs
  have hsecond := (hG.congr_of_eventuallyEq heqG).unique hGs
  have hp : radialSpectralPressure n z r=
      2*((n+radialInnerShootingThreshold : ℕ) : ℝ)*‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold)) := by
    dsimp only [radialSpectralPressure,radialShootingA]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  constructor
  · dsimp only [radialComplexAngularAction]
    rw [hp]
    dsimp only [radialMatchedGaugeFirstSource,radialMassDensity,radialMassFlux,
      radialMatchedMassFunction,radialAngularDensity] at hfirst ⊢
    dsimp only [radialMatchedVelocity] at *
    push_cast at hfirst ⊢
    linear_combination -hfirst
  · dsimp only [radialComplexAngularAction]
    dsimp only [radialMatchedGaugeSecondSource,radialMassDensity,radialMassFlux,
      radialMatchedMassFunction,radialAngularDensity] at hsecond ⊢
    dsimp only [radialMatchedVelocity] at *
    push_cast at hsecond ⊢
    linear_combination -hsecond

end DefocusingNLS

end OAI
