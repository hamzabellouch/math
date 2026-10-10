import OAI.Analysis.LipschitzHilbert.Trees.SourceParameters
import OAI.Analysis.LipschitzHilbert.Estimates.ShortTimeParameters

namespace OAI

/-! The actual dyadic source parameters meet the counting hypotheses. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert.SourceParameters

theorem blockCount_pos {L : ℝ} (hL : 1 < L) : 0 < blockCount L := by
  apply Nat.one_le_ceil_iff.mpr
  exact sq_pos_of_pos (Real.log_pos hL)

theorem one_lt_step {L : ℝ} (hL : 0 < L) : 1 < step L := by
  apply (Real.log_pos_iff (step_pos L).le).mp
  exact (Real.rpow_pos_of_pos hL _).trans_le (log_step_bounds hL.le).1

theorem one_lt_branching {L : ℝ} (hL : 1 < L) : 1 < branching L :=
  one_lt_pow₀ (one_lt_step (zero_lt_one.trans hL)) (Nat.ne_of_gt (blockCount_pos hL))

theorem log_branching_lower {L : ℝ} (hL : 1 < L) :
    L ^ (7 / 10 : ℝ) ≤ Real.log (branching L) := by
  have hstep := one_lt_step (zero_lt_one.trans hL)
  have hK : (1 : ℝ) ≤ blockCount L := by exact_mod_cast blockCount_pos hL
  calc
    L ^ (7 / 10 : ℝ) ≤ Real.log (step L) := (log_step_bounds (zero_lt_one.trans hL).le).1
    _ ≤ (blockCount L : ℝ) * Real.log (step L) :=
      le_mul_of_one_le_left (Real.log_nonneg hstep.le) hK
    _ = Real.log (branching L) := (Real.log_pow _ _).symm

theorem eventually_branching_ge (c : ℝ) : ∀ᶠ L : ℝ in atTop, c ≤ branching L := by
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)).eventually_ge_atTop
      (Real.log (max c 1))] with L hL hpow
  have hmax : 0 < max c 1 := zero_lt_one.trans_le (le_max_right _ _)
  apply (le_max_left c 1).trans
  exact (Real.log_le_log_iff hmax (branching_pos L)).mp
    (hpow.trans (log_branching_lower (by linarith)))

/-- For every fixed enlargement and polynomial, the actual integer bin
count and the manuscript's width/cutoff scales satisfy all numerical
conditions used in the simultaneous count. -/
theorem eventually_count_parameters (p c C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
      1 < branching L ∧ 0 < (branchingNat L) ^ 2 ∧
      c ≤ ((branchingNat L) ^ 2 : ℕ) ∧
      (((branchingNat L) ^ 2 : ℕ) : ℝ) = branching L ^ 2 ∧
      ∀ m tau : ℝ,
        Real.exp (L ^ (9 / 10 : ℝ)) ≤ m →
        m ≤ 2 * Real.exp (L ^ (9 / 10 : ℝ)) →
        0 ≤ tau → tau ≤ Real.exp (-(L ^ (97 / 100 : ℝ))) →
        branching L ^ 2 ≤ m ∧
        ∀ ell : ℝ, 0 ≤ ell → ell ≤ tau → C * L ^ p * m * ell ≤ 1 / 2 := by
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_branching_ge c,
    eventually_branching_separation, LipschitzHilbert.eventually_transfer_small_time p C hC]
    with L hL hc hsep htime
  have hB : 1 < branching L := one_lt_branching (by linarith)
  have hBN : 0 < branchingNat L := by
    have : (0 : ℝ) < branchingNat L := by rw [branchingNat_cast]; exact branching_pos L
    exact_mod_cast this
  have hcast : (((branchingNat L) ^ 2 : ℕ) : ℝ) = branching L ^ 2 := by
    rw [Nat.cast_pow, branchingNat_cast]
  have hBsq : branching L ≤ branching L ^ 2 := le_self_pow₀ hB.le (by norm_num)
  refine ⟨hB, pow_pos hBN _, ?_, hcast, ?_⟩
  · rw [hcast]
    exact hc.trans hBsq
  · intro m tau hml hmu ht htu
    have hm : 0 ≤ m := (Real.exp_pos _).le.trans hml
    refine ⟨(pow_le_pow_right₀ hB.le (by norm_num : 2 ≤ 100)).trans (hsep.trans hml), ?_⟩
    exact fun ell he het => htime m tau ell hm hmu ht htu he het

end LipschitzHilbert.SourceParameters

end

end OAI
