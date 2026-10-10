import OAI.Combinatorics.ContingencyTables.Dense.GridAdjacency
import OAI.Combinatorics.ContingencyTables.Transport.MetropolisChain
import Mathlib.Data.Nat.Log

namespace OAI

/-! # The actual dyadic axis-proposal chain -/

namespace ContingencyTables.GridBoundary

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

def binProposal (d : ℕ) : ℝ := 1 / (2 : ℝ) ^ Nat.clog 2 (8 * d)

theorem binProposal_bounds (d : ℕ) (hd : 14 ≤ d) :
    0 < binProposal d ∧ 1 / (16 * (d : ℝ)) ≤ binProposal d ∧
      binProposal d ≤ 1 / (8 * (d : ℝ)) := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hn : 1 < 8 * d := by omega
  have hlow := Nat.le_pow_clog (by decide : 1 < 2) (8 * d)
  have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hn
  have hpos := Nat.clog_pos (by decide : 1 < 2) hn
  have hupp : 2 ^ Nat.clog 2 (8 * d) ≤ 16 * d := by
    have heq : 2 ^ Nat.clog 2 (8 * d) = 2 ^ (Nat.clog 2 (8 * d)).pred * 2 := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
      exact pow_succ _ _
    rw [heq]
    omega
  have hlow' : 8 * (d : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 (8 * d) := by exact_mod_cast hlow
  have hupp' : (2 : ℝ) ^ Nat.clog 2 (8 * d) ≤ 16 * (d : ℝ) := by exact_mod_cast hupp
  refine ⟨by unfold binProposal; positivity, ?_, ?_⟩
  · exact one_div_le_one_div_of_le (by positivity) hupp'
  · exact one_div_le_one_div_of_le (by positivity) hlow'

theorem binProposal_degree (q d : ℕ) (hd : 14 ≤ d) (hq : q ≤ d) :
    ((2 * q : ℕ) : ℝ) * binProposal d ≤ 1 / 4 := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hqd : (q : ℝ) ≤ d := by exact_mod_cast hq
  have hb := binProposal_bounds d hd
  calc
    _ ≤ (2 * (q : ℝ)) * (1 / (8 * (d : ℝ))) := by
      push_cast
      exact mul_le_mul_of_nonneg_left hb.2.2 (by positivity)
    _ ≤ (2 * (d : ℝ)) * (1 / (8 * (d : ℝ))) := by gcongr
    _ = 1 / 4 := by field_simp; ring

def gridChain {q K : ℕ} (d : ℕ) (hd : 14 ≤ d) (hq : q ≤ d) (hK : 1 ≤ K)
    (w : Grid (I := Fin q) K → ℝ) (hw : ∀ a, 0 < w a) : FiniteChain (Grid (I := Fin q) K) := by
  letI : Nonempty (Grid (I := Fin q) K) := ⟨fun _ => ⟨0, by constructor <;> omega⟩⟩
  exact MetropolisChain.chain w hw Neighbor neighbor_symm (binProposal d)
    (binProposal_bounds d hd).1.le (2 * q) (fun a => by simpa using neighbor_degree a)
    ((binProposal_degree q d hd hq).trans (by norm_num))

theorem gridChain_pi {q K : ℕ} (d : ℕ) (hd : 14 ≤ d) (hq : q ≤ d) (hK : 1 ≤ K)
    (w : Grid (I := Fin q) K → ℝ) (hw : ∀ a, 0 < w a) (a : Grid (I := Fin q) K) :
    (gridChain d hd hq hK w hw).π a = w a / (∑ b, w b) := rfl

end

end ContingencyTables.GridBoundary

end OAI
