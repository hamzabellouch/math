import OAI.NumberTheory.JointDickman.Analysis.PerronLeftDecay

namespace OAI

/-! # Exponential decay of the truncated Perron tails -/
namespace JointDickman
open Filter Asymptotics
open scoped Topology

theorem perronScale_tail_scalar_decay (b : ℝ) :
    (fun q : ℝ => (Real.exp q/2)^(-1/2:ℝ)) =o[atTop] (fun q => q^b) := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop (by norm_num : (0:ℝ) < 1/2) b).const_mul_left
    (1/(2:ℝ)^(-1/2:ℝ))
  apply h.congr_left
  intro q
  rw [Real.div_rpow (Real.exp_pos q).le (by norm_num),←Real.exp_mul]
  rw [show -(1/2:ℝ)*q = q*(-1/2) by ring]
  ring

end JointDickman

end OAI
