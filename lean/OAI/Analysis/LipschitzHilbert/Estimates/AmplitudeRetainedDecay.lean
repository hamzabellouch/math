import OAI.Analysis.LipschitzHilbert.Estimates.RetainedAmplitudeMatrix

namespace OAI

/-! The retained amplitude loss is linear in the logarithmic disparity,
so the model's L^-20 saving leaves L^-19 after reconstruction. -/
noncomputable section
namespace LipschitzHilbert

theorem retainedAmplitudeCost_sq (C0 L : ℝ) (hC0 : 0≤C0) (hL : 0≤L) :
    (retainedAmplitudeCost C0 L)^2=128*C0*(2*(L/Real.log 2)+5) := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  unfold retainedAmplitudeCost
  simp only [mul_pow]
  rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),
    Real.sq_sqrt (by positivity : 0≤2*(L/Real.log 2)+5),
    Real.sq_sqrt (by positivity : 0≤4*C0)]
  ring

theorem retainedAmplitudeCost_decay (K C0 L : ℝ) (hK : 0≤K) (hC0 : 0≤C0) (hL : 1≤L) :
    K*L^(-20:ℝ)*(retainedAmplitudeCost C0 L)^2≤
      (128*K*C0*(2/Real.log 2+5))*L^(-19:ℝ) := by
  have hLp : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hT : 2*(L/Real.log 2)+5≤(2/Real.log 2+5)*L := by
    calc
      _=(2/Real.log 2)*L+5 := by ring
      _≤(2/Real.log 2)*L+5*L := by linarith
      _=_ := by ring
  have hp : L^(-20:ℝ)*L=L^(-19:ℝ) := by
    calc
      _=L^(-20:ℝ)*L^(1:ℝ) := by rw [Real.rpow_one]
      _=L^((-20:ℝ)+1) := (Real.rpow_add hLp _ _).symm
      _=_ := by norm_num
  rw [retainedAmplitudeCost_sq C0 L hC0 hLp.le]
  calc
    _=128*K*C0*(L^(-20:ℝ)*(2*(L/Real.log 2)+5)) := by ring
    _≤128*K*C0*(L^(-20:ℝ)*((2/Real.log 2+5)*L)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT (Real.rpow_nonneg hLp.le _)) (by positivity)
    _=_ := by
      calc
        _=(128*K*C0*(2/Real.log 2+5))*(L^(-20:ℝ)*L) := by ring
        _=_ := by rw [hp]

end LipschitzHilbert

end

end OAI
