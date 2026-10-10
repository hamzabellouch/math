import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! The scalar exponent calculation in the three-halves dual estimate. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem cubic_duality_estimate (F J E : ℝ) (hF : 0≤F) (hJ : 0≤J) (hE : 0≤E)
    (h : J≤F^(2/3:ℝ)*(E*J)^(1/3:ℝ)) : J≤(E+1)^(3/2:ℝ)*F := by
  have hcube := pow_le_pow_left₀ hJ h 3
  have hFp : (F^(2/3:ℝ))^3=F^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hF]
    norm_num
  have hEJp : ((E*J)^(1/3:ℝ))^3=E*J := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (mul_nonneg hE hJ)]
    norm_num
  rw [mul_pow,hFp,hEJp] at hcube
  by_cases hz : J=0
  · rw [hz]
    positivity
  have hJp : 0<J := lt_of_le_of_ne hJ (Ne.symm hz)
  have hs : J^2≤E*F^2 := by
    by_contra hn
    have hp : 0<J*(J^2-E*F^2) := mul_pos hJp (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith [hcube]
  have hcoef : E≤(E+1)^3 := by nlinarith [sq_nonneg E,pow_nonneg hE 3]
  have hpower : ((E+1)^(3/2:ℝ)*F)^2=(E+1)^3*F^2 := by
    rw [mul_pow,←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0≤E+1)]
    norm_num
  apply (sq_le_sq₀ hJ (by positivity : 0≤(E+1)^(3/2:ℝ)*F)).mp
  rw [hpower]
  exact hs.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg F))

end LipschitzHilbert.PacketRepresentation

end

end OAI
