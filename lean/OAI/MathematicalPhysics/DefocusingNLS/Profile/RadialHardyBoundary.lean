import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialHardyInequality

namespace OAI

/-! The uniform Hardy inequality with its outgoing boundary trace retained. -/

open Set
open scoped ContDiff
namespace DefocusingNLS

theorem radialHardyInequality_boundary (a R : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1/2)
    (hR : 0 ≤ R) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    16*(∫ r in (0 : ℝ)..R, r^9*radialHardyWeight a r*(f r)^2) ≤
      (∫ r in (0 : ℝ)..R, r^11*radialHardyWeight a r*(deriv f r)^2)+
        4*radialHardyFlux a R*(f R)^2 := by
  let A : ℝ → ℝ := fun r => r^9*radialHardyWeight a r*(f r)^2
  let B : ℝ → ℝ := fun r => r^11*radialHardyWeight a r*(deriv f r)^2
  let C : ℝ → ℝ := fun r => radialHardyFlux a r*f r*deriv f r
  let D : ℝ → ℝ := fun r => deriv (radialHardyFlux a) r*(f r)^2
  have hρ := radialHardyWeight_continuous a
  have hfd := hf.continuous_deriv_one
  have hwd := radialHardyFlux_deriv_continuous a
  have hw : Continuous (radialHardyFlux a) := by
    unfold radialHardyFlux
    fun_prop
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hB : Continuous B := by dsimp [B]; fun_prop
  have hC : Continuous C := by dsimp [C]; fun_prop
  have hD : Continuous D := by dsimp [D]; fun_prop
  have hAi := hA.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := R)
  have hBi := hB.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := R)
  have hCi := hC.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := R)
  have hDi := hD.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := R)
  have hboundary : (∫ r in (0 : ℝ)..R, D r+2*C r)=radialHardyFlux a R*(f R)^2 := by
    have hder (r : ℝ) : HasDerivAt (fun t => radialHardyFlux a t*(f t)^2)
        (D r+2*C r) r := by
      have hh := (radialHardyFlux_hasDerivAt a r).mul
        (((hf.differentiable (by norm_num) r).hasDerivAt).pow 2)
      apply hh.congr_deriv
      dsimp [D,C]
      rw [(radialHardyFlux_hasDerivAt a r).deriv]
      norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
      ring
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => hder r) (hDi.add (hCi.const_mul 2))
    simpa only [radialHardyFlux_zero,zero_mul,sub_zero] using he
  have hboundary' : (∫ r in (0 : ℝ)..R, D r)+2*(∫ r in (0 : ℝ)..R, C r)=radialHardyFlux a R*(f R)^2 := by
    rw [intervalIntegral.integral_add hDi (hCi.const_mul 2),
      intervalIntegral.integral_const_mul] at hboundary
    exact hboundary
  have hmono : 8*(∫ r in (0 : ℝ)..R, A r) ≤ ∫ r in (0 : ℝ)..R, D r := by
    have hm := intervalIntegral.integral_mono_on hR (hAi.const_mul 8) hDi
      (fun r hr => show 8*A r ≤ D r from by
        dsimp [A,D]
        have hh := mul_le_mul_of_nonneg_right (radialHardyFlux_deriv_lower a r ha ha1 hr.1)
          (sq_nonneg (f r))
        nlinarith [hh])
    simpa only [intervalIntegral.integral_const_mul] using hm
  have hnonneg : 0 ≤ ∫ r in (0 : ℝ)..R, (B r+8*C r)+16*A r := by
    apply intervalIntegral.integral_nonneg hR
    intro r hr
    have hh := mul_nonneg
      (mul_nonneg (pow_nonneg hr.1 9) (radialHardyWeight_pos a r).le)
      (sq_nonneg (r*deriv f r+4*f r))
    dsimp [A,B,C,radialHardyFlux]
    convert hh using 1
    ring
  rw [intervalIntegral.integral_add (hBi.add (hCi.const_mul 8)) (hAi.const_mul 16),
    intervalIntegral.integral_add hBi (hCi.const_mul 8),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hnonneg
  change 16*(∫ r in (0 : ℝ)..R, A r) ≤
    (∫ r in (0 : ℝ)..R, B r)+4*radialHardyFlux a R*(f R)^2
  linarith


end DefocusingNLS

end OAI
