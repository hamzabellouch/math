import OAI.Combinatorics.ContingencyTables.Sampling.SmallChainBudget
import Mathlib.Data.Nat.Log

namespace OAI

/-! # The manuscript's exact dyadic small-chain proposal -/

namespace ContingencyTables

noncomputable def smallProposal (d : ℕ) : ℝ := 1/(2:ℝ)^(Nat.clog 2 (32*d^2))

lemma smallProposal_bounds (d : ℕ) (hd : 1 ≤ d) :
    0 < smallProposal d ∧ 1/(64*(d:ℝ)^2) ≤ smallProposal d ∧
      smallProposal d ≤ 1/(32*(d:ℝ)^2) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hn : 1 < 32*d^2 := by nlinarith
  have hlo := Nat.le_pow_clog (by decide : 1 < 2) (32*d^2)
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hn
  have he : 2^Nat.clog 2 (32*d^2) = 2^(Nat.clog 2 (32*d^2)).pred*2 := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos (Nat.clog_pos (by decide : 1 < 2) hn)]
    exact pow_succ _ _
  have hhi : 2^Nat.clog 2 (32*d^2) ≤ 64*d^2 := by rw [he]; omega
  have hloR : 32*(d:ℝ)^2 ≤ (2:ℝ)^Nat.clog 2 (32*d^2) := by exact_mod_cast hlo
  have hhiR : (2:ℝ)^Nat.clog 2 (32*d^2) ≤ 64*(d:ℝ)^2 := by exact_mod_cast hhi
  refine ⟨by unfold smallProposal; positivity,?_,?_⟩
  · exact one_div_le_one_div_of_le (by positivity) hhiR
  · exact one_div_le_one_div_of_le (by positivity) hloR

lemma smallProposal_degree (d : ℕ) (hd : 1 ≤ d) :
    ((5*d^2+1:ℕ):ℝ)*smallProposal d ≤ 1/2 := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsq : (1:ℝ) ≤ (d:ℝ)^2 := by exact_mod_cast (show 1 ≤ d^2 by nlinarith)
  have hm := mul_le_mul_of_nonneg_left (smallProposal_bounds d hd).2.2
    (show (0:ℝ) ≤ (5*d^2+1:ℕ) by positivity)
  apply hm.trans
  rw [mul_one_div]
  apply (div_le_iff₀ (show (0:ℝ) < 32*(d:ℝ)^2 by positivity)).mpr
  push_cast
  nlinarith

lemma smallProposal_poincare_budget (d : ℕ) (hd : 14 ≤ d) :
    2*(770*(d:ℝ)^4*((d^20:ℕ):ℝ)^6)/smallProposal d ≤ (d:ℝ)^160 := by
  have hp := smallProposal_bounds d (by omega)
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hrecip : 1/smallProposal d ≤ 64*(d:ℝ)^2 := by
    apply (div_le_iff₀ hp.1).mpr
    have hh := (div_le_iff₀ (show (0:ℝ) < 64*(d:ℝ)^2 by positivity)).mp hp.2.1
    nlinarith
  calc
    _ = (2*(770*(d:ℝ)^4*((d^20:ℕ):ℝ)^6))*(1/smallProposal d) := by ring
    _ ≤ (2*(770*(d:ℝ)^4*((d^20:ℕ):ℝ)^6))*(64*(d:ℝ)^2) :=
      mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ = 128*(d:ℝ)^2*(770*(d:ℝ)^4*((d^20:ℕ):ℝ)^6) := by ring
    _ ≤ _ := small_chain_poincare_constant d hd

end ContingencyTables

end OAI
