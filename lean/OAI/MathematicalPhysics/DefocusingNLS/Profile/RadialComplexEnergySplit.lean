import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialGaugeEnergy

namespace OAI

/-! The full weighted H1/angular normalization splits exactly into its
zero-pressure gradient form and the two weighted value masses. -/

open Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem radialComplexEnergy_one_split (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (eta R : ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) :
    (∫ r in (0 : ℝ)..R, radialMassDensity n z r*(‖f r‖^2+‖deriv f r‖^2)+
      eta*radialAngularDensity n z r*‖f r‖^2) =
      radialComplexAngularForm n z eta R (fun _ => 0) f+
      (∫ r in (0 : ℝ)..R, radialMassDensity n z r*‖f r‖^2) := by
  have hM := radialMassDensity_continuous n z hX hz
  have hK := radialAngularDensity_continuous n z hX hz
  have hv : IntervalIntegrable (fun r => radialMassDensity n z r*‖f r‖^2) volume 0 R :=
    (hM.mul (hf.continuous.norm.pow 2)).intervalIntegrable 0 R
  have hd : IntervalIntegrable (fun r => radialMassDensity n z r*‖deriv f r‖^2) volume 0 R :=
    (hM.mul (hf.continuous_deriv_one.norm.pow 2)).intervalIntegrable 0 R
  have ha : IntervalIntegrable (fun r => radialAngularDensity n z r*‖f r‖^2) volume 0 R :=
    (hK.mul (hf.continuous.norm.pow 2)).intervalIntegrable 0 R
  rw [radialComplexAngularForm_zero_eq n z hX hz eta R f hf]
  calc
    _ = ∫ r in (0 : ℝ)..R, (radialMassDensity n z r*‖f r‖^2+
        radialMassDensity n z r*‖deriv f r‖^2)+eta*(radialAngularDensity n z r*‖f r‖^2) := by
      apply intervalIntegral.integral_congr
      intro r _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hv.add hd) (ha.const_mul eta),
        intervalIntegral.integral_add hv hd,intervalIntegral.integral_const_mul]
      ring

theorem radialComplexEnergy_split (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (eta R : ℝ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    (∫ r in (0 : ℝ)..R, radialMatchedMassFunction n z r*spectralRadialEnergyDensity eta f g r) =
      (radialComplexAngularForm n z eta R (fun _ => 0) f+
        radialComplexAngularForm n z eta R (fun _ => 0) g)+
      (∫ r in (0 : ℝ)..R, radialMassDensity n z r*‖f r‖^2)+
      (∫ r in (0 : ℝ)..R, radialMassDensity n z r*‖g r‖^2) := by
  have hM := radialMassDensity_continuous n z hX hz
  have hK := radialAngularDensity_continuous n z hX hz
  have hi (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) : IntervalIntegrable (fun r =>
      radialMassDensity n z r*(‖u r‖^2+‖deriv u r‖^2)+eta*radialAngularDensity n z r*‖u r‖^2) volume 0 R := by
    have hd := hu.continuous_deriv_one
    have hc := hu.continuous
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    _ = ∫ r in (0 : ℝ)..R,
        (radialMassDensity n z r*(‖f r‖^2+‖deriv f r‖^2)+eta*radialAngularDensity n z r*‖f r‖^2)+
        (radialMassDensity n z r*(‖g r‖^2+‖deriv g r‖^2)+eta*radialAngularDensity n z r*‖g r‖^2) := by
      apply intervalIntegral.integral_congr
      intro r _
      dsimp only [radialMassDensity,radialAngularDensity,radialMatchedMassFunction,
        spectralRadialEnergyDensity,spectralCoordinateEnergy]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hi f hf) (hi g hg),
        radialComplexEnergy_one_split n z hX hz eta R f hf,
        radialComplexEnergy_one_split n z hX hz eta R g hg]
      ring

end DefocusingNLS

end OAI
