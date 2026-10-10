import OAI.NumberTheory.TotientAsymptotic.CandidateHeadSeparation

namespace OAI

/-! The candidate tail is smaller than every fixed power of the ambient scale. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma subpower_log_eventually_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,(Real.log x)^(4/5:ℝ) ≤ ε*Real.log x := by
  filter_upwards [subpower_log_ratio.eventually (eventually_lt_nhds hε),
    eventually_gt_atTop (1:ℝ)] with x hx hx1
  exact (div_le_iff₀ (Real.log_pos hx1)).mp hx.le

lemma capped_tail_subpower {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,∀ n : ℕ,n ≤ m x → ∀ p : Fin n → ℕ,
      (∀ i,(p i).Prime) → (∀ i,primePrefixCoord p i ≤ (19/25:ℝ)*B x) →
      ((∏ i,p i:ℕ):ℝ) ≤ x^ε := by
  filter_upwards [capped_tail_denominator_budget 1,subpower_log_eventually_le hε,
    eventually_gt_atTop (1:ℝ)] with x hx hpower hx1
  intro n hn p hp hcap
  have hr : (0:ℝ) < (∏ i,p i:ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => (hp i).pos)
  have htail := prime_tail_log_bound p hp hcap
  have hdim := mul_le_mul_of_nonneg_right (show (n:ℝ) ≤ m x by exact_mod_cast hn)
    (Real.exp_pos ((19/25:ℝ)*B x)).le
  norm_num only [Nat.cast_one,Real.log_one,zero_add] at hx
  have hlog : Real.log ((∏ i,p i:ℕ):ℝ) ≤ ε*Real.log x :=
    htail.trans (hdim.trans (hx.trans hpower))
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hr] at he
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx1)]
  simpa only [mul_comm] using he

lemma subpower_head_lower {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,∀ D : ℝ,1 ≤ D →
      Real.log D ≤ (Real.log x)^(4/5:ℝ) →
      ∀ q ∈ primeInterval (x/(2*D)) (x/D),x^(1-ε) < (q:ℝ) := by
  have hconst : Tendsto (fun x : ℝ => Real.log 2/Real.log x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  filter_upwards [subpower_log_eventually_le (half_pos hε),
    hconst.eventually (eventually_lt_nhds (half_pos hε)),
    eventually_gt_atTop (1:ℝ)] with x hsmall hconst hx1
  intro D hD hlog q hq
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have htwo : Real.log 2 ≤ (ε/2)*Real.log x :=
    (div_le_iff₀ hlogx).mp hconst.le
  have hargument : (1-ε)*Real.log x ≤ Real.log (x/(2*D)) := by
    rw [Real.log_div hx0.ne' (mul_pos (by norm_num) hD0).ne',
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hD0.ne']
    linarith only [hsmall,hlog,htwo]
  have hp := Real.exp_le_exp.mpr hargument
  rw [Real.exp_log (div_pos hx0 (mul_pos (by norm_num) hD0))] at hp
  have hroot : x^(1-ε) ≤ x/(2*D) := by
    rw [Real.rpow_def_of_pos hx0]
    simpa only [mul_comm] using hp
  exact hroot.trans_lt (mem_head_prime_interval hx0.le hD0 hq).2.1

end TotientAsymptotic

end

end OAI
