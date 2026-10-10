import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexDilationIdentity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexVirialCoercivity

namespace OAI

/-! The actual complex virial identity controls both gradient energies by
its cross pairing, explicit boundary terms and the first-component mass. -/

open Set Filter MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_dilation_bulk_bound :
    ∃ k : ℝ, 0 < k ∧ ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ eta R : ℝ, 0 ≤ eta → 0 ≤ R →
      ∀ (lam : ℂ) (f g : ℝ → ℂ), ContDiff ℝ 2 f → ContDiff ℝ 2 g →
      IsRadialLogGaugeEigenpair (n+radialInnerShootingThreshold)
        (radialMatchedEvenProfile n z) (eta : ℂ) lam f g →
      k*(radialComplexAngularForm n z eta R (fun _ => 0) f+
        radialComplexAngularForm n z eta R (fun _ => 0) g) ≤
      ((lam-(((6-2*radialShootingA n)/2 : ℝ) : ℂ))*
        radialComplexDilationPairing n z R ((6-2*radialShootingA n)/2) f g).re-
      radialComplexAngularBoundary n z eta R ((6-2*radialShootingA n)/2) (radialSpectralPressure n z) f-
      radialComplexAngularBoundary n z eta R ((6-2*radialShootingA n)/2) (fun _ => 0) g+
      800*(∫ r in (0 : ℝ)..R, radialMassDensity n z r*‖f r‖^2) := by
  obtain ⟨k,hk,hdef⟩ := radialMatched_uniform_deformation
  refine ⟨k,hk,?_⟩
  filter_upwards [hdef,radialMatched_global_pressure_transport_bound] with n hn hp
  intro z hX hz eta R heta hR lam f g hf hg he
  have hdq := radialSpectralPressure_deriv_continuousOn n z hX hz R
  have hvel r (hr : r ∈ Icc 0 R) : k ≤ deriv (radialMatchedVelocity n z) r ∧
      k ≤ radialMatchedVelocityRatio n z r := hn z hX hz r hr.1
  have hpress r (hr : r ∈ Icc 0 R) :
      radialMatchedVelocity n z r*deriv (radialSpectralPressure n z) r ≤ 1600 := hp z hX hz r hr.1
  have hfp := radialComplexShiftedVirial_coercive n z hX hz eta R k 1600 heta hR
    (radialSpectralPressure n z) (deriv (radialSpectralPressure n z)) f
    (hf.of_le (by norm_num)) hdq hvel hpress
  have hgp := radialComplexShiftedVirial_coercive n z hX hz eta R k 0 heta hR
    (fun _ => 0) (fun _ => 0) g (hg.of_le (by norm_num)) continuousOn_const hvel (by simp)
  norm_num only [show (1600 : ℝ)/2=800 by norm_num,zero_div,zero_mul,add_zero] at hfp hgp
  have hid := radialMatched_complex_dilation_identity n z hX hz eta R
    ((6-2*radialShootingA n)/2) hR lam f g hf hg he
  linarith only [hfp,hgp,hid]

end DefocusingNLS

end OAI
