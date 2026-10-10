import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeDiscardedSum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! The allowed exp(O(L^0.9)) amplitude bound is absorbed by the
exp(-L/8) discarded-mass saving. -/
noncomputable section
open Filter
namespace LipschitzHilbert

theorem eventually_amplitude_tail_decay (A B C : ℝ) (hA : 0<A) (_hB : 0≤B) (hC : 0<C) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℝ, Q≤A*Real.exp (B*L^(9/10:ℝ)) →
      C*Q*Real.exp (-L/8)≤Real.exp (-L/16) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).eventually_ge_atTop (32*B),
    eventually_ge_atTop (32*|Real.log (C*A)|)] with L hL hgap hconstant Q hQ
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hpow : L=L^(9/10:ℝ)*L^(1/10:ℝ) := by
    rw [←Real.rpow_add hLp]
    norm_num
  have hslow : B*L^(9/10:ℝ)≤L/32 := by
    have h := mul_le_mul_of_nonneg_left hgap (Real.rpow_nonneg hLp.le (9/10:ℝ))
    rw [←hpow] at h
    nlinarith
  have hlog : Real.log (C*A)≤L/32 := by
    have h := le_abs_self (Real.log (C*A))
    linarith
  calc
    C*Q*Real.exp (-L/8)≤C*(A*Real.exp (B*L^(9/10:ℝ)))*Real.exp (-L/8) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ hC.le) (Real.exp_pos _).le
    _=Real.exp (Real.log (C*A)+B*L^(9/10:ℝ)-L/8) := by
      rw [sub_eq_add_neg,Real.exp_add,Real.exp_add,Real.exp_log (mul_pos hC hA),neg_div]
      ring
    _≤Real.exp (-L/16) := Real.exp_le_exp.mpr (by linarith)

end LipschitzHilbert

end

end OAI
