import OAI.NumberTheory.TotientAsymptotic.BootstrapCutoffs
import OAI.NumberTheory.TotientAsymptotic.UniformNonNormalCount

namespace OAI

/-! The normality parameter chosen for the bootstrap gives exponential decay
in the log-log scale. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma loglogCutoff_ge_four {b : ℝ} (hb : 2 ≤ b) : 4 ≤ loglogCutoff b := by
  have he : 3 ≤ Real.exp b := by linarith [Real.add_one_le_exp b]
  apply Nat.le_floor
  have hh := Real.add_one_le_exp (Real.exp b)
  norm_num
  linarith

lemma bootstrap_normality_factor {b : ℝ} (hb : 300000000 ≤ b) :
    let S := loglogCutoff (bootstrapBottom b)
    2 < (S:ℝ) ∧ 0 ≤ B S ∧
      (Real.log S)^(-1/6:ℝ) ≤ Real.exp (1/3:ℝ)*Real.exp (-b/600000000) := by
  let L := bootstrapBottom b
  have hL : 2 ≤ L := Nat.le_floor (show (2:ℝ) ≤ b/100000000 by linarith)
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hB := loglogCutoff_bounds hLR
  have h4 := loglogCutoff_ge_four hLR
  have hS : (2:ℝ) < loglogCutoff L := by exact_mod_cast (show 2 < loglogCutoff L by omega)
  have hlog : 0 < Real.log (loglogCutoff L) := Real.log_pos (by linarith)
  have hBlower : b/100000000-2 ≤ B (loglogCutoff L) := by
    have hh : b/100000000-1 < (L:ℝ) := Nat.sub_one_lt_floor (b/100000000)
    linarith only [hh,hB.2.1]
  refine ⟨hS,by linarith only [hB.2.1,hLR],?_⟩
  rw [Real.rpow_def_of_pos hlog,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change B (loglogCutoff L)*(-1/6:ℝ) ≤ (1/3:ℝ)+ -b/600000000
  linarith

lemma shifted_sixth_exp_decay {c : ℝ} (hc : 0 < c) :
    Tendsto (fun b : ℝ => (b+2)^6*Real.exp (-c*b)) atTop (nhds 0) := by
  have ht : Tendsto (fun b : ℝ => b+2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro t
    filter_upwards [eventually_ge_atTop (t-2)] with b hb
    linarith
  have hh := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (6:ℝ) c hc).comp ht).const_mul
    (Real.exp (2*c))
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [] with b
  have he : Real.exp (-c*b)=Real.exp (2*c)*Real.exp (-c*(b+2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only [Function.comp_apply]
  have hpow : (b+2)^(6:ℝ)=(b+2)^(6:ℕ) := Real.rpow_natCast (b+2) 6
  rw [hpow,he]
  ring

end TotientAsymptotic

end

end OAI
