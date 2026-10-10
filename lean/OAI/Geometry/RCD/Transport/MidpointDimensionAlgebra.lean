import OAI.Geometry.RCD.Harmonic.LogCosQuadratic

namespace OAI

/-! # Scalar algebra for the full-to-reduced midpoint comparison -/

open Set
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem half_power_reciprocal {C : ℝ} (hC : 0 < C) (p : ℝ) :
    (1/2:ℝ)^p*(1/(2*C))^(1-p) = (1/2)/C^(1-p) := by
  rw [show 1/(2*C)=(1/2:ℝ)*C⁻¹ by ring,Real.mul_rpow (by norm_num) (inv_nonneg.mpr hC.le),
    ←mul_assoc,←Real.rpow_add (by norm_num : (0:ℝ)<1/2),
    show p+(1-p)=1 by ring,Real.rpow_one,Real.inv_rpow hC.le,div_eq_mul_inv]
  rfl

theorem dimension_scaled_sqrt {N : ℝ} (hN : 1 < N) (A : ℝ) :
    Real.sqrt (1-1/N)*Real.sqrt (A/(N-1)) = Real.sqrt (A/N) := by
  have hN0 : 0 < N := by linarith
  have hq : 0 ≤ 1-1/N := sub_nonneg.mpr ((div_le_one hN0).mpr hN.le)
  rw [←Real.sqrt_mul hq]
  congr 1
  field_simp [hN0.ne', (sub_pos.mpr hN).ne']

theorem cosh_dimension_rpow {c x : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hx : 0 ≤ x) :
    (Real.cosh x)^c ≤ Real.cosh (Real.sqrt c*x) := by
  have h := Real.exp_le_exp.mpr (log_cosh_sqrt_mul_ge hc0 hc1 hx)
  rw [Real.exp_log (Real.cosh_pos _)] at h
  simpa only [Real.rpow_def_of_pos (Real.cosh_pos x),mul_comm] using h

theorem cos_dimension_rpow {c x : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hx : 0 ≤ x) (hxp : x < Real.pi/2) :
    (Real.cos x)^c ≤ Real.cos (Real.sqrt c*x) := by
  have hp : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hxp⟩
  have hs1 : Real.sqrt c ≤ 1 := by nlinarith [Real.sq_sqrt hc0,Real.sqrt_nonneg c]
  have hy : Real.sqrt c*x < Real.pi/2 := (mul_le_of_le_one_left hx hs1).trans_lt hxp
  have hpy : 0 < Real.cos (Real.sqrt c*x) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.sqrt_nonneg c,Real.pi_pos],hy⟩
  have h := Real.exp_le_exp.mpr (log_cos_sqrt_mul_ge hc0 hc1 hx hxp)
  rw [Real.exp_log hpy] at h
  simpa only [Real.rpow_def_of_pos hp,mul_comm] using h

theorem tau_midpoint_of_sigma {K N θ C : ℝ} (hC : 0 < C)
    (hs : sigma K N (1/2) θ = ENNReal.ofReal (1/(2*C))) :
    tau K N (1/2) θ = ENNReal.ofReal ((1/2)/C^(1-1/N)) := by
  unfold tau
  norm_num only [show (1/2:ℝ)≠0 by norm_num,show (1/2:ℝ)≠1 by norm_num,ite_false]
  rw [hs,ENNReal.ofReal_rpow_of_pos (by norm_num : (0:ℝ)<1/2),
    ENNReal.ofReal_rpow_of_pos (by positivity : 0 < 1/(2*C)),
    ←ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),half_power_reciprocal hC]

end RegularPointCoordinates

end

end OAI
