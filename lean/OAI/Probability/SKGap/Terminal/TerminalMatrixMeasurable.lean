import Mathlib
import OAI.Probability.SKGap.Localization.LiteralRegularity
import OAI.Probability.SKGap.Terminal.TerminalRates

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory Real Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

lemma continuous_coupling_entry (i k : Fin n) : Continuous (fun g : Disorder n=>coupling g i k) := by
  unfold coupling
  split_ifs <;> fun_prop

lemma continuous_coupling_matrix : Continuous (fun g : Disorder n=>Matrix.of (coupling g)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  exact continuous_coupling_entry i

lemma continuous_tanh_real : Continuous tanh :=
  continuous_iff_continuousAt.mpr (fun x=>(hasDerivAt_tanh x).continuousAt)

lemma continuous_terminalU : Continuous (terminalU (n:=n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  exact continuous_tanh_real.comp (continuous_coupling_entry i k)

lemma continuous_terminalQ : Continuous (terminalQ (n:=n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  exact (continuous_tanh_real.comp (continuous_coupling_entry i k)).pow 2

lemma continuous_principalOperatorNorm (S : Finset (Fin n)) :
    Continuous (fun M : Matrix (Fin n) (Fin n) ℝ=>principalOperatorNorm M S) := by
  unfold principalOperatorNorm
  exact (continuous_matrixOperator.comp (by unfold Matrix.submatrix;fun_prop)).norm

lemma terminalMatrixData_measurable (M α ε : ℝ) :
    MeasurableSet {g : Disorder n | terminalMatrixData M α ε g} := by
  classical
  unfold terminalMatrixData
  simp only [ofPred_and,ofPred_forall]
  apply MeasurableSet.inter
    (MeasurableSet.iInter (fun i=>MeasurableSet.iInter (fun k=>measurableSet_le (continuous_coupling_entry i k).abs.measurable measurable_const)))
  apply MeasurableSet.inter (measurableSet_le continuous_coupling_matrix.norm.measurable measurable_const)
  apply MeasurableSet.inter (measurableSet_le continuous_terminalU.norm.measurable measurable_const)
  apply MeasurableSet.inter (measurableSet_le continuous_terminalQ.norm.measurable measurable_const)
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro i
    apply measurableSet_le _ measurable_const
    exact (continuous_finsetSum _ (fun k _=>(continuous_tanh_real.comp (continuous_coupling_entry i k)).pow 4)).measurable
  · apply MeasurableSet.iInter
    intro S
    apply MeasurableSet.iInter
    intro _
    exact (measurableSet_le ((continuous_principalOperatorNorm S).comp continuous_terminalU).measurable measurable_const).inter
      (measurableSet_le ((continuous_principalOperatorNorm S).comp continuous_terminalQ).measurable measurable_const)
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Filter Real
open scoped Topology

lemma nat_pow_exp_div_tendsto {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Tendsto (fun n : ℕ=>(n:ℝ)^k*exp (-(n:ℝ)/c)) atTop (𝓝 0) := by
  convert nat_pow_exp_neg_tendsto (inv_pos.mpr hc) k using 1
  ext n
  congr 2
  ring

lemma nat_pow_exp_sqrt_div_tendsto {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Tendsto (fun n : ℕ=>(n:ℝ)^k*exp (-sqrt (n:ℝ)/c)) atTop (𝓝 0) := by
  convert nat_pow_exp_sqrt_tendsto (inv_pos.mpr hc) k using 1
  ext n
  congr 2
  ring

lemma terminalRawTail_tendsto {j α ε l : ℝ} (hj : 0 < j)
    (h₅ : 0 < ε^2/(36*π^2*j)-(l*α+log (1+exp (-l))))
    (h₆ : 0 < ε/(4*j)-(l*α+log (1+exp (-l))+α*log 2)) :
    Tendsto (fun n : ℕ=>terminalRawTail j α ε n l) atTop (𝓝 0) := by
  have ht1 := (nat_pow_exp_div_tendsto (by positivity : 0 < π^2*j) 0).const_mul 2
  have ht2 := (nat_pow_exp_sqrt_div_tendsto (by positivity : 0 < 8*j) 1).const_mul 2
  have ht3 := (nat_pow_exp_sqrt_div_tendsto (by positivity : 0 < 4*j) 2).const_mul 2
  have ht4 := nat_pow_exp_neg_tendsto (by norm_num : (0:ℝ) < 1) 1
  have ht5 := (nat_pow_exp_neg_tendsto h₅ 0).const_mul 2
  have ht6 := nat_pow_exp_neg_tendsto h₆ 1
  have hh := ((((ht1.add ht2).add ht3).add ht4).add ht5).add ht6
  simpa only [terminalRawTail,pow_zero,pow_one,one_mul,mul_zero,add_zero,neg_mul,mul_assoc,mul_comm,mul_left_comm,mul_neg,mul_neg_one,zero_mul,mul_one] using hh
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Filter Real
open scoped Topology

lemma sparse_parameters {j ε : ℝ} (hj : 0 < j) (hε : 0 < ε) :
    ∃ α l : ℝ,0 < α ∧ α < 1/2 ∧ 0 ≤ l ∧ 2*sqrt (j*α) ≤ ε/6 ∧
      0 < ε^2/(36*π^2*j)-(l*α+log (1+exp (-l))) ∧
      0 < ε/(4*j)-(l*α+log (1+exp (-l))+α*log 2) := by
  let δ := min (ε^2/(72*π^2*j)) (ε/(8*j))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have ht : Tendsto (fun l : ℝ=>log (1+exp (-l))) atTop (𝓝 0) := by
    have hplus : Tendsto (fun l : ℝ=>1+exp (-l)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.add tendsto_exp_neg_atTop_nhds_zero : Tendsto (fun l : ℝ=>1+exp (-l)) atTop (𝓝 (1+0)))
    have h := (continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp hplus
    simpa only [Function.comp_def, log_one] using h
  obtain ⟨l,hl,hlδ⟩ := ((eventually_ge_atTop (0:ℝ)).and (ht.eventually (gt_mem_nhds (by linarith only [hδ] : (0:ℝ) < δ/2)))).exists
  let α := min (1/4:ℝ) (min (ε^2/(144*j)) (δ/(2*(l+log 2+1))))
  have hlog : (0:ℝ) ≤ log 2 := log_nonneg (by norm_num)
  have hden : 0 < 2*(l+log 2+1) := by linarith only [hl,hlog]
  have hα : 0 < α := lt_min (by norm_num) (lt_min (by positivity) (div_pos hδ hden))
  have hαmax : α ≤ 1/4 := min_le_left _ _
  have hαedge : α ≤ ε^2/(144*j) := (min_le_right _ _).trans (min_le_left _ _)
  have hαrate : α ≤ δ/(2*(l+log 2+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hprod : α*(l+log 2+1) ≤ δ/2 := by
    have h := (le_div_iff₀ hden).mp hαrate
    nlinarith only [h]
  have hedge : 2*sqrt (j*α) ≤ ε/6 := by
    have hm := (le_div_iff₀ (by positivity : 0 < 144*j)).mp hαedge
    have hs := sq_sqrt (mul_nonneg hj.le hα.le)
    nlinarith only [hm,hs,sqrt_nonneg (j*α),hε]
  refine ⟨α,l,hα,(by linarith only [hαmax]),hl,hedge,?_,?_⟩
  · have hδ1 : δ ≤ ε^2/(72*π^2*j) := min_le_left _ _
    have ha := mul_nonneg hα.le hlog
    have he : ε^2/(36*π^2*j)=2*(ε^2/(72*π^2*j)) := by ring
    rw [he]
    nlinarith only [hδ1,hδ,hprod,hlδ,ha,hα]
  · have hδ2 : δ ≤ ε/(8*j) := min_le_right _ _
    have he : ε/(4*j)=2*(ε/(8*j)) := by ring
    rw [he]
    nlinarith only [hδ2,hδ,hprod,hlδ,hα]
end SKGap

end
end

end OAI
