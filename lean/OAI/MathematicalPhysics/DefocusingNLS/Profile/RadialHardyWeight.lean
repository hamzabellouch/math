import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialWeightComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace OAI

/-! The radial Hardy weight in dimension twelve, with its exact flux derivative. -/

open scoped ContDiff
namespace DefocusingNLS

noncomputable def radialHardyWeight (a r : ℝ) : ℝ := (1+r^2)^(-2*a)

noncomputable def radialHardyFlux (a r : ℝ) : ℝ := r^10*radialHardyWeight a r

theorem radialHardyWeight_pos (a r : ℝ) : 0 < radialHardyWeight a r :=
  Real.rpow_pos_of_pos (by positivity) _

theorem radialHardyWeight_hasDerivAt (a r : ℝ) :
    HasDerivAt (radialHardyWeight a)
      (-4*a*r/(1+r^2)*radialHardyWeight a r) r := by
  have hb : 0 < 1+r^2 := by positivity
  have h := (((hasDerivAt_id r).pow 2).const_add 1).rpow_const
    (p := -2*a) (Or.inl hb.ne')
  apply h.congr_deriv
  simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,
    Real.rpow_sub_one hb.ne']
  unfold radialHardyWeight
  ring

theorem radialHardyWeight_continuous (a : ℝ) : Continuous (radialHardyWeight a) :=
  continuous_iff_continuousAt.mpr (fun r => (radialHardyWeight_hasDerivAt a r).continuousAt)

theorem radialHardyFlux_hasDerivAt (a r : ℝ) :
    HasDerivAt (radialHardyFlux a)
      (r^9*radialHardyWeight a r*(10-4*a*r^2/(1+r^2))) r := by
  have h := ((hasDerivAt_id r).pow 10).mul (radialHardyWeight_hasDerivAt a r)
  apply h.congr_deriv
  norm_num only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,one_mul,mul_one]
  ring

theorem radialHardyFlux_deriv_lower (a r : ℝ) (_ha : 0 ≤ a) (ha1 : a ≤ 1/2)
    (hr : 0 ≤ r) :
    8*r^9*radialHardyWeight a r ≤ deriv (radialHardyFlux a) r := by
  rw [(radialHardyFlux_hasDerivAt a r).deriv]
  have hb : 0 < 1+r^2 := by positivity
  have hq : 4*a*r^2/(1+r^2) ≤ 2 := by
    apply (div_le_iff₀ hb).mpr
    nlinarith [sq_nonneg r,mul_nonneg (show 0 ≤ 2-4*a by linarith) (sq_nonneg r)]
  have hm := mul_le_mul_of_nonneg_left (show 8 ≤ 10-4*a*r^2/(1+r^2) by linarith)
    (mul_nonneg (pow_nonneg hr 9) (radialHardyWeight_pos a r).le)
  nlinarith

theorem radialHardyFlux_zero (a : ℝ) : radialHardyFlux a 0=0 := by
  simp [radialHardyFlux]

end DefocusingNLS

end OAI
