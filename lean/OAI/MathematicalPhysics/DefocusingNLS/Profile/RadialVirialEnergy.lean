import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVelocityCalculus

namespace OAI

/-! Weighted virial integration for the radial differential expression. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialDriftDensity (n : ℕ) (z : ProfileMatchingBall) (r : ℝ) : ℝ :=
  (6-2*radialShootingA n)/2*radialMassDensity n z r-
    radialMassSlope n z r*radialMatchedVelocity n z r

theorem radialDriftDensity_eq (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : 0 ≤ r) :
    radialDriftDensity n z r=radialMassDensity n z r*
      (deriv (radialMatchedVelocity n z) r-(6-2*radialShootingA n)/2) := by
  have h := radialMassSlope_velocity n z hX hz r hr
  unfold radialDriftDensity
  linarith

theorem radialDriftDensity_continuousOn (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) :
    ContinuousOn (radialDriftDensity n z) (Icc 0 R) :=
  ((radialMassDensity_continuous n z hX hz).continuousOn.const_mul _).sub
    ((radialMassSlope_continuousOn n z hX hz R).mul
      (radialMatchedVelocity_continuousOn n z hX hz R))

theorem radialMatched_virial_energy (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 ≤ R)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hdfR : deriv f R=0) :
    (∫ r in (0 : ℝ)..R, radialMatchedVelocity n z r*deriv f r*
      radialMassLaplacian n z f r)=
        ∫ r in (0 : ℝ)..R, radialDriftDensity n z r*(deriv f r)^2 := by
  let B := fun r => radialMassFlux n z r*deriv f r*deriv (deriv f) r
  let C := fun r => radialMassSlope n z r*radialMatchedVelocity n z r*(deriv f r)^2
  let D := fun r => radialMassDensity n z r*(deriv f r)^2
  have hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have h1 := hd.continuous
  have h2 := hd.continuous_deriv_one
  have hBi : IntervalIntegrable B MeasureTheory.volume 0 R := (((radialMassFlux_continuousOn n z hX hz R).mul h1.continuousOn).mul
    h2.continuousOn).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hR
  have hCi : IntervalIntegrable C MeasureTheory.volume 0 R := (((radialMassSlope_continuousOn n z hX hz R).mul
    (radialMatchedVelocity_continuousOn n z hX hz R)).mul
    (h1.pow 2).continuousOn).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hR
  have hDi : IntervalIntegrable D MeasureTheory.volume 0 R := ((radialMassDensity_continuous n z hX hz).mul (h1.pow 2)).intervalIntegrable
    (μ := MeasureTheory.volume) 0 R
  have hi (r : ℝ) : radialMatchedVelocity n z r*deriv f r*
      radialMassLaplacian n z f r= -B r-C r := by
    dsimp [B,C,radialMassLaplacian,radialMassFlux,radialMatchedVelocity]
    ring
  have ht := radialMatched_transport_integration n z hX hz R hR (deriv f) hd hdfR
  change 2*(∫ r in (0 : ℝ)..R, B r)=-(6-2*radialShootingA n)*(∫ r in (0 : ℝ)..R, D r) at ht
  have he : (∫ r in (0 : ℝ)..R, radialDriftDensity n z r*(deriv f r)^2)=
      (6-2*radialShootingA n)/2*(∫ r in (0 : ℝ)..R, D r)-∫ r in (0 : ℝ)..R, C r := by
    have hh (r : ℝ) : radialDriftDensity n z r*(deriv f r)^2=
        (6-2*radialShootingA n)/2*D r-C r := by
      dsimp [radialDriftDensity,C,D]
      ring
    simp_rw [hh]
    rw [intervalIntegral.integral_sub (hDi.const_mul _) hCi,intervalIntegral.integral_const_mul]
  simp_rw [hi]
  have hsplit := intervalIntegral.integral_sub hBi.neg hCi
  simp only [Pi.neg_apply,intervalIntegral.integral_neg] at hsplit
  rw [hsplit,he]
  linarith

end DefocusingNLS

end OAI
