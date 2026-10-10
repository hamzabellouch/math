import OAI.NumberTheory.Jacobsthal.Conclusions.IteratedLogScales

namespace OAI

namespace Erdos970.NumberTheoryLean.IteratedLogBudget

open _root_.Filter IteratedLogScales JacobsthalTerminalScales
open JacobsthalSurvivorScale JacobsthalDeletionBudget ProgressionSieve
open scoped Topology

/-- The revised cutoff makes the deletion loss smaller than the old, already
proved survivor lower bound. The factor `A` is chosen before the limit. -/
theorem separation (c : ℝ) (hc : 0 < c) :
    ∃ A : ℝ, 3 ≤ A ∧ ∀ᶠ k : ℝ in atTop,
      k * deletionBudget (terminalY (rescale A k)) (terminalCutoff (rescale A k)) <
        c * ((terminalY (rescale A k) : ℝ) *
          SmallSieveFinite.smallEuler ⌊ErdosInverseBoxHeight.sourceW
            (terminalTop (rescale A k))⌋₊ /
          (ErdosInverseBoxHeight.sourceB (terminalTop (rescale A k))) ^ 2) := by
  let c0 : ℝ := Real.exp (-Real.eulerMascheroniConstant) / 2
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  let A : ℝ := max 3 ((4 * 1276 * 32) / (c * c0))
  have hA : 3 ≤ A := le_max_left _ _
  have hA0 : 0 < A := by linarith
  have hAb : 4 * 1276 * 32 ≤ A * (c * c0) :=
    (div_le_iff₀ (mul_pos hc hc0)).mp (le_max_right _ _)
  have hcoef : 4 * 1275 / A < c * c0 / 32 := by
    apply (div_lt_iff₀ hA0).mpr
    nlinarith
  refine ⟨A, hA, ?_⟩
  have hu := rescale_tendsto A hA
  have hWT := JacobsthalBudgetSeparation.terminal_w_tendsto.comp hu
  filter_upwards [hu.eventually eventual_terminal_numerics,
    hu.eventually eventual_terminal_logs,
    hWT.eventually ErdosInverseEuler.smallEuler_log_bounds,
    eventual_loglog_bounds, eventual_loglog_le_logW A hA] with k hn hl he hk hll
  let u := rescale A k
  let w := ErdosInverseBoxHeight.sourceW (terminalTop u)
  obtain ⟨hx, hlog, hlogs, _hTop, hYlo, _hYhi, _hTcut, hT, hTL⟩ := hn
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hlog0 : 0 < Real.log u := by linarith
  have hw2 : 2 ≤ w := he.1
  have hw : 1 < w := by linarith
  have hlogw : 0 < Real.log w := Real.log_pos hw
  have hV : c0 / Real.log w ≤
      SmallSieveFinite.smallEuler ⌊w⌋₊ := by
    calc
      _ = Real.exp (-Real.eulerMascheroniConstant) / (2 * Real.log w) := by
        dsimp [c0]
        ring
      _ ≤ _ := he.2.2.1
  have hscale := normalized_scale_lower hu0 hlog0 hl.2.2.2.2.1 hl.2.2.2.2.2
    hw hc0 hYlo hV
  have hbudget := source_deletion_budget hu0 hlog0 hlogs
    (terminalY u) (terminalCutoff u) hT hTL
  have hf : 1275 * loglog k / A < c * c0 * Real.log w / 32 := by
    calc
      _ ≤ 1275 * (4 * Real.log w) / A :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hll (by norm_num)) hA0.le
      _ = (4 * 1275 / A) * Real.log w := by ring
      _ < (c * c0 / 32) * Real.log w := mul_lt_mul_of_pos_right hcoef hlogw
      _ = _ := by ring
  have hden : 0 < u ^ 2 / (Real.log u) ^ 2 :=
    div_pos (sq_pos_of_pos hu0) (sq_pos_of_pos hlog0)
  calc
    k * deletionBudget (terminalY u) (terminalCutoff u) =
        (loglog k / A) * (u * deletionBudget (terminalY u) (terminalCutoff u)) := by
      dsimp [u, rescale]
      field_simp [hA0.ne', hk.2.1.ne']
    _ ≤ (loglog k / A) * (1275 * u ^ 2 / (Real.log u) ^ 2) :=
      mul_le_mul_of_nonneg_left hbudget (div_pos hk.2.1 hA0).le
    _ = (1275 * loglog k / A) * (u ^ 2 / (Real.log u) ^ 2) := by ring
    _ < (c * c0 * Real.log w / 32) * (u ^ 2 / (Real.log u) ^ 2) :=
      mul_lt_mul_of_pos_right hf hden
    _ = c * (c0 * u ^ 2 * Real.log w / (32 * (Real.log u) ^ 2)) := by ring
    _ ≤ c * ((terminalY u : ℝ) * SmallSieveFinite.smallEuler ⌊w⌋₊ /
        (Real.log (terminalTop u) / Real.log w) ^ 2) :=
      mul_le_mul_of_nonneg_left hscale hc.le
    _ = _ := rfl

end Erdos970.NumberTheoryLean.IteratedLogBudget

end OAI
