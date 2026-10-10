import Mathlib

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

def lowerGapScale (A J:ℝ):ℝ := Real.exp (-(A+2*J/3))
def upperGapScale (A J:ℝ):ℝ := Real.exp (-(A+J/3))

lemma gap_scale_ratios (A J:ℝ) :
    Real.exp (-(A+J))/lowerGapScale A J=Real.exp (-J/3) ∧
    lowerGapScale A J/upperGapScale A J=Real.exp (-J/3) ∧
    upperGapScale A J/Real.exp (-A)=Real.exp (-J/3) := by
  simp only [lowerGapScale,upperGapScale,←Real.exp_sub]
  constructor
  · congr 1; ring
  constructor <;> congr 1 <;> ring

lemma exists_uniform_plateau_smallness {C eps:ℝ} (hC:0 ≤ C) (heps:0 < eps) :
    ∃J:ℝ,4 ≤ J ∧ Real.exp (2/J) ≤ 1+eps ∧
    ∀A D:ℝ,J^2 ≤ A → 0 < D → |Real.log D| ≤ C+A/J^2+J⁻¹ →
      Real.exp (-(A+J)) ≤ eps*lowerGapScale A J ∧
      lowerGapScale A J ≤ eps*upperGapScale A J ∧
      upperGapScale A J ≤ eps*Real.exp (-A) ∧
      (∀k:ℕ,k ≤ 2 → upperGapScale A J ≤ eps*D^k) := by
  have ht : Tendsto (fun J:ℝ=>Real.exp (2*C+2-J/3)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    simpa only [sub_eq_add_neg,Function.comp_def,id_eq] using tendsto_const_nhds.add_atBot
      (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<3)))
  have hr : Tendsto (fun J:ℝ=>Real.exp (-J/3)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    simpa only [Function.comp_def,neg_div,id_eq] using
      (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<3)))
  have hd : Tendsto (fun J:ℝ=>Real.exp (2/J)) atTop (𝓝 1) := by
    simpa only [Real.exp_zero,Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp
      (show Tendsto (fun J:ℝ=>2/J) atTop (𝓝 0) from tendsto_const_nhds.div_atTop tendsto_id)
  obtain ⟨J,hJ,Ht,Hr,Hd⟩ := ((eventually_ge_atTop (4:ℝ)).and
    ((ht.eventually (gt_mem_nhds heps)).and
    ((hr.eventually (gt_mem_nhds heps)).and (hd.eventually (gt_mem_nhds (by linarith : (1:ℝ)<1+eps)))))).exists
  refine ⟨J,hJ,Hd.le,?_⟩
  intro A D hA hD hlog
  have hJ0:0 < J:=by linarith
  have hJ2:16 ≤ J^2:=by nlinarith only [hJ]
  have hA0:0 ≤ A:=(sq_nonneg J).trans hA
  have hfrac:A/J^2 ≤ A/16:=by
    apply div_le_div_of_nonneg_left hA0 (by norm_num) hJ2
  have hinv:J⁻¹ ≤ 1:=by exact inv_le_one_of_one_le₀ (by linarith)
  have hlog': -(C+A/16+1) ≤ Real.log D:=by
    have H:=neg_abs_le (Real.log D)
    linarith only [H,hlog,hfrac,hinv]
  obtain ⟨H1,H2,H3⟩:=gap_scale_ratios A J
  refine ⟨?_,?_,?_,?_⟩
  · exact (div_le_iff₀ (Real.exp_pos _)).mp (H1.le.trans Hr.le)
  · exact (div_le_iff₀ (Real.exp_pos _)).mp (H2.le.trans Hr.le)
  · exact (div_le_iff₀ (Real.exp_pos _)).mp (H3.le.trans Hr.le)
  · intro k hk
    have hex : -(A+J/3)-(k:ℝ)*Real.log D ≤ 2*C+2-J/3 := by
      interval_cases k <;> norm_num <;> nlinarith only [hlog',hA0,hC]
    have He:= (Real.exp_le_exp.mpr hex).trans Ht.le
    have heq: Real.exp (-(A+J/3)-(k:ℝ)*Real.log D)=upperGapScale A J/D^k := by
      rw [Real.exp_sub,Real.exp_nat_mul,Real.exp_log hD]
      rfl
    rw [heq] at He
    exact (div_le_iff₀ (pow_pos hD k)).mp He

end WeakMTWTransport

end
end

end OAI
