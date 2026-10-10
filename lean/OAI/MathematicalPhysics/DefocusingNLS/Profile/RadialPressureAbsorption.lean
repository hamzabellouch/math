import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedHardy

namespace OAI

/-! The transported pressure is absorbed by the actual radial energy form. -/

open Set Filter
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_pressure_energy_absorption :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ R : ℝ, 0 ≤ R → ∀ f : ℝ → ℝ,
      ContDiff ℝ 1 f → f R=0 →
      let μ := fun r => ‖radialMatchedProfile n z r‖^2
      let V := fun r => ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold))/
        radialShootingA n
      let w := radialVelocity (6-2*radialShootingA n) (fun r => ‖radialMatchedProfile n z r‖)
      2*(∫ r in (0 : ℝ)..R, r^11*μ r*(w r*deriv V r)*(f r)^2) ≤
        (∫ r in (0 : ℝ)..R, r^11*μ r*V r*(f r)^2)+
        (∫ r in (0 : ℝ)..R, r^11*μ r*(deriv f r)^2) := by
  obtain ⟨d,hd,hH⟩ := radialMatched_uniform_Hardy
  let ε := min (1/2 : ℝ) (d/18)
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hd (by norm_num))
  have hε1 : ε ≤ 1/2 := min_le_left _ _
  have hεd : 18*ε ≤ d := by
    have h := min_le_right (1/2 : ℝ) (d/18)
    dsimp [ε]
    linarith
  filter_upwards [hH,radialMatched_pressure_form_small ε hε]
    with n hn hs z hX hz R hR f hf hfR
  let μ := fun r => ‖radialMatchedProfile n z r‖^2
  let V := fun r => ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold))/
    radialShootingA n
  let w := radialVelocity (6-2*radialShootingA n) (fun r => ‖radialMatchedProfile n z r‖)
  let A := fun r => r^9*μ r*(f r)^2
  let B := fun r => r^11*μ r*(deriv f r)^2
  let P := fun r => r^11*μ r*V r*(f r)^2
  let T := fun r => r^11*μ r*(w r*deriv V r)*(f r)^2
  have hQ := (radialMatchedProfile_differentiable n z hX hz).continuous
  have hμ : Continuous μ := hQ.norm.pow 2
  have hV : Continuous V := (hQ.norm.pow _).div_const _
  have hfd := hf.continuous_deriv_one
  have hT0 : ContinuousOn (fun r => w r*deriv V r) (Icc 0 R) :=
    radialMatchedPressureTransport_continuousOn n z hX hz R
  have hAc : Continuous A := by dsimp [A]; fun_prop
  have hBc : Continuous B := by dsimp [B]; fun_prop
  have hPc : Continuous P := by dsimp [P]; fun_prop
  have hTc : ContinuousOn T (Icc 0 R) := by
    exact ((continuous_id.pow 11).continuousOn.mul hμ.continuousOn).mul hT0 |>.mul
      (hf.continuous.pow 2).continuousOn
  have hAi := hAc.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := R)
  have hPi := hPc.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := R)
  have hTi := hTc.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hR
  have hpoint : ∀ r ∈ Icc 0 R, T r ≤ ε*(P r+A r) := by
    intro r hr
    have hh := mul_le_mul_of_nonneg_right (hs z hX hz r hr.1)
      (mul_nonneg (mul_nonneg (pow_nonneg hr.1 9) (sq_nonneg ‖radialMatchedProfile n z r‖))
        (sq_nonneg (f r)))
    change r^2*(w r*deriv V r)*(r^9*μ r*(f r)^2) ≤
      ε*(r^2*V r+1)*(r^9*μ r*(f r)^2) at hh
    dsimp [T,P,A]
    convert hh using 1 <;> ring
  have hbound := intervalIntegral.integral_mono_on hR hTi ((hPi.add hAi).const_mul ε) hpoint
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add hPi hAi] at hbound
  have hhardy := hn z hX hz R hR f hf hfR
  change d*(∫ r in (0 : ℝ)..R, A r) ≤ 9*(∫ r in (0 : ℝ)..R, B r) at hhardy
  have hAn : 0 ≤ ∫ r in (0 : ℝ)..R, A r :=
    intervalIntegral.integral_nonneg hR (fun r hr => by
      have hr0 : 0 ≤ r := hr.1
      dsimp [A,μ]
      positivity)
  have hPn : 0 ≤ ∫ r in (0 : ℝ)..R, P r :=
    intervalIntegral.integral_nonneg hR (fun r hr => by
      have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
      have hr0 : 0 ≤ r := hr.1
      dsimp [P,μ,V]
      positivity)
  have hsmallA := mul_le_mul_of_nonneg_right hεd hAn
  have hsmallP := mul_le_mul_of_nonneg_right hε1 hPn
  change 2*(∫ r in (0 : ℝ)..R, T r) ≤
    (∫ r in (0 : ℝ)..R, P r)+(∫ r in (0 : ℝ)..R, B r)
  nlinarith

end DefocusingNLS

end OAI
