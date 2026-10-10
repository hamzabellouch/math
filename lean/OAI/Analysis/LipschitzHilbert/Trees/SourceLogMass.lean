import OAI.Analysis.LipschitzHilbert.Trees.ResidualBudget

namespace OAI

/-! Leave one exponential unit of slack when choosing the source parameter.
This absorbs the polynomial factor in the joined concentration theorem. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_source_log_mass (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ mass ratio : ℝ,
      mass ≤ ratio*L^C → ratio ≤ Real.exp L →
      Real.log (max 1 mass) ≤ 2*L := by
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1)).bound
    (show 0 < 1/(|C|+1) by positivity)
  filter_upwards [hlog,eventually_ge_atTop (1:ℝ)] with L hlog hL
  intro mass ratio hmass hratio
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hlog0 := Real.log_nonneg hL
  have hCL : C*Real.log L ≤ L := by
    rw [Real.rpow_one,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hlog0,
      abs_of_pos hL0] at hlog
    have hC : C ≤ |C|+1 := (le_abs_self C).trans (by linarith [abs_nonneg C])
    have hden : 0 < |C|+1 := by positivity
    have hb : (|C|+1)*Real.log L ≤ L := by
      calc
        _ ≤ (|C|+1)*(1/(|C|+1)*L) := mul_le_mul_of_nonneg_left hlog hden.le
        _ = L := by field_simp
    exact (mul_le_mul_of_nonneg_right hC hlog0).trans hb
  have hm : mass ≤ Real.exp (2*L) := by
    calc
      mass ≤ ratio*L^C := hmass
      _ ≤ Real.exp L*L^C := mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hL0.le _)
      _ = Real.exp (L+C*Real.log L) := by
        rw [Real.rpow_def_of_pos hL0,Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (2*L) := Real.exp_le_exp.mpr (by linarith)
  have hm' : max 1 mass ≤ Real.exp (2*L) :=
    max_le (Real.one_le_exp (by linarith)) hm
  exact (Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hm').trans_eq
    (Real.log_exp _)

end LipschitzHilbert

end

end OAI
