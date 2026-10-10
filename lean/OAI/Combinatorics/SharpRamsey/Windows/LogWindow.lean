import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.CostContraction

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

lemma eventually_log_window (C a : ℝ) (hC : 0<C) (ha : 0≤a) :
    ∀ᶠ σ : ℝ in atTop, ∀ x : ℝ, 0≤x → x≤C*exp σ*σ^a →
      log (x+1)≤(a+2)*σ := by
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop (log (C+1))]
    with σ hσ hCσ x hx hxup
  have hσ0 : 0<σ:=by linarith
  have he : 1≤exp σ:=one_le_exp hσ0.le
  have hp : 1≤σ^a:=one_le_rpow hσ ha
  have hup : x+1≤(C+1)*exp σ*σ^a := by
    have hh : 1≤exp σ*σ^a:=one_le_mul_of_one_le_of_one_le he hp
    nlinarith only [hxup,hh]
  have hl:=log_le_log (by linarith : 0<x+1) hup
  rw [log_mul (mul_ne_zero (by linarith : C+1≠0) (exp_ne_zero _))
    (rpow_pos_of_pos hσ0 a).ne',log_mul (by linarith : C+1≠0) (exp_ne_zero _),
    log_exp,log_rpow hσ0] at hl
  have hs : log σ≤σ:= (log_le_sub_one_of_pos hσ0).trans (by linarith)
  have hhs:=mul_le_mul_of_nonneg_left hs ha
  nlinarith only [hl,hCσ,hhs]
end
end SharpLogRamsey.SourceScales

end

end OAI
