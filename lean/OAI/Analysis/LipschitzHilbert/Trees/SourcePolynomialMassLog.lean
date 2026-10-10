import OAI.Analysis.LipschitzHilbert.Trees.SourceLogMass

namespace OAI

/-! The polynomial mass cap in §11 fits in log U ≤ 3L when log N ≤ 2L. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_source_polynomial_mass_log (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ N : ℝ, 0 < N → Real.log N ≤ 2*L →
      Real.log (L^C*N) ≤ 3*L := by
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1)).bound
    (show 0 < 1/(|C|+1) by positivity)
  filter_upwards [hlog,eventually_ge_atTop (1:ℝ)] with L hlog hL
  intro N hN hlogN
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hlog0 := Real.log_nonneg hL
  rw [Real.rpow_one,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hlog0,
    abs_of_pos hL0] at hlog
  have hden : 0 < |C|+1 := by positivity
  have hb : (|C|+1)*Real.log L ≤ L := by
    calc
      _ ≤ (|C|+1)*(1/(|C|+1)*L) := mul_le_mul_of_nonneg_left hlog hden.le
      _ = L := by field_simp
  have hCL : C*Real.log L ≤ L :=
    (mul_le_mul_of_nonneg_right ((le_abs_self C).trans (by linarith)) hlog0).trans hb
  rw [Real.log_mul (Real.rpow_pos_of_pos hL0 C).ne' hN.ne',Real.log_rpow hL0]
  linarith

end LipschitzHilbert

end

end OAI
