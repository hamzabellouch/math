import OAI.NumberTheory.TotientAsymptotic.QuarterPowerBudget

namespace OAI

/-! The smooth residual mass is summable against terminal-coordinate decay. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def terminalMassWeight (c : ℝ) (k : ℕ) : ℝ :=
  Real.exp (10*(Real.log ((k:ℝ)+5))^2-c*k)

lemma terminalMassWeight_pos (c : ℝ) (k : ℕ) : 0 < terminalMassWeight c k := Real.exp_pos _

theorem summable_terminalMassWeight {c : ℝ} (hc : 0 < c) :
    Summable (terminalMassWeight c) := by
  let q := Real.exp (-c/2)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hc])
  apply (summable_geometric_of_lt_one hq0 hq1).of_norm_bounded_eventually_nat
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (((10000*((0:ℝ)+31)^2)/(c/4))^(4/3:ℝ))),
    eventually_ge_atTop (1:ℕ)] with k hk hk1
  have hk0 : (1:ℝ) ≤ k := by exact_mod_cast hk1
  have hb : 1 ≤ (k:ℝ)+1 := by linarith only [hk0]
  have hthreshold : ((10000*((0:ℝ)+31)^2)/(c/4))^(4/3:ℝ) ≤ (k:ℝ)+1 := by
    linarith only [hk]
  have hbudget := four_thirds_threshold_budget hb (le_refl (0:ℝ))
    (show 0 < c/4 by linarith only [hc]) hthreshold
  have hlog : 0 ≤ Real.log ((k:ℝ)+5) := Real.log_nonneg (by linarith only [hk0])
  have he : 10*(Real.log ((k:ℝ)+5))^2-c*k ≤ -(c/2)*(k:ℝ) := by
    simp only [add_zero] at hbudget
    rw [show (k:ℝ)+1+4=(k:ℝ)+5 by ring] at hbudget
    have hh : c/4*((k:ℝ)+1) ≤ (c/2)*(k:ℝ) := by nlinarith only [hc,hk0]
    nlinarith only [hbudget,hh,hlog,sq_nonneg (Real.log ((k:ℝ)+5))]
  rw [Real.norm_eq_abs,abs_of_pos (terminalMassWeight_pos c k)]
  dsimp only [terminalMassWeight,q]
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  nlinarith only [he]

lemma finite_terminal_mass_bound {c : ℝ} (hc : 0 < c) (I : Finset ℕ) :
    (∑ k ∈ I,terminalMassWeight c k) ≤ ∑' k : ℕ,terminalMassWeight c k :=
  (summable_terminalMassWeight hc).sum_le_tsum _ (fun k _ => (terminalMassWeight_pos c k).le)

end TotientAsymptotic

end

end OAI
