import OAI.Analysis.LipschitzHilbert.Trees.ResidualBudget

namespace OAI

/-! The actual terminal cost remains negligible against the bad-top
threshold, for every fixed mass-cutoff exponent. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

 theorem eventually_source_stop_cost_small (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop, ∀ α : ℝ, 1 ≤ α → α ≤ 3 →
      (1+(L^C)^(Real.sqrt L)*(L^A+1)^(α-1))*Real.exp (-L) ≤ 1/2 := by
  let d := C+2*A+1
  have hd : 0 < d := by dsimp [d]; linarith
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).bound
    (show 0 < 1/(4*d) by positivity)
  have hdecay1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 1 (by norm_num : (0:ℝ) < 1)
  have hdecay2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (3/4)
    (by norm_num : (0:ℝ) < 3/4)
  filter_upwards [eventually_ge_atTop (1:ℝ),hlog,
    hdecay1.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4)),
    hdecay2.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/16))]
    with L hL hl hsmall1 hsmall2
  intro α hα hα3
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hs : 1 ≤ Real.sqrt L := (Real.one_le_sqrt).mpr hL
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL
  rw [Real.norm_eq_abs,abs_of_nonneg hlog0,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _),← Real.sqrt_eq_rpow] at hl
  have hexponent : C*Real.sqrt L*Real.log L+2*A*Real.log L ≤ L/4 := by
    have h1 : C*Real.sqrt L+2*A ≤ d*Real.sqrt L := by
      have hA' := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*A)
      dsimp [d]
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ d*Real.sqrt L)
    have hsquare := Real.sq_sqrt hL0.le
    have heq : d*Real.sqrt L*(1/(4*d)*Real.sqrt L) = L/4 := by
      field_simp [hd.ne']
      nlinarith
    calc
      _ = (C*Real.sqrt L+2*A)*Real.log L := by ring
      _ ≤ (d*Real.sqrt L)*Real.log L := mul_le_mul_of_nonneg_right h1 hlog0
      _ ≤ L/4 := h2.trans_eq heq
  have hbase : 1 ≤ L^A+1 := by
    have := Real.rpow_nonneg hL0.le A
    linarith
  have hpow : (L^A+1)^(α-1) ≤ 4*L^(2*A) := by
    calc
      _ ≤ (L^A+1)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
      _ ≤ (2*L^A)^(2:ℝ) := Real.rpow_le_rpow (by positivity)
        (by have := Real.one_le_rpow hL hA; linarith) (by norm_num)
      _ = 4*L^(2*A) := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_nonneg hL0.le _),
          Real.rpow_two,← Real.rpow_mul hL0.le]
        norm_num [show A*2 = 2*A by ring]
  have hcost : (L^C)^(Real.sqrt L)*(L^A+1)^(α-1) ≤ 4*Real.exp (L/4) := by
    calc
      _ ≤ (L^C)^(Real.sqrt L)*(4*L^(2*A)) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (Real.rpow_nonneg hL0.le _) _)
      _ = 4*((L^C)^(Real.sqrt L)*L^(2*A)) := by ring
      _ = 4*Real.exp (C*Real.sqrt L*Real.log L+2*A*Real.log L) := by
        congr 1
        rw [← Real.rpow_mul hL0.le,← Real.rpow_add hL0,Real.rpow_def_of_pos hL0]
        congr 1
        ring
      _ ≤ 4*Real.exp (L/4) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)
  simp only [Real.rpow_zero,one_mul,neg_mul] at hsmall1 hsmall2
  calc
    _ ≤ (1+4*Real.exp (L/4))*Real.exp (-L) :=
      mul_le_mul_of_nonneg_right (add_le_add le_rfl hcost) (Real.exp_pos _).le
    _ = Real.exp (-L)+4*Real.exp (-(3/4:ℝ)*L) := by
      rw [add_mul,one_mul,mul_assoc,← Real.exp_add,
        show L/4 + -L = -(3/4:ℝ)*L by ring]
    _ ≤ 1/2 := by
      simp only [neg_mul]
      linarith

end LipschitzHilbert

end

end OAI
