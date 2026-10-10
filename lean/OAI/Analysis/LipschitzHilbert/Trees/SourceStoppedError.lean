import OAI.Analysis.LipschitzHilbert.Estimates.NestedPerturbation
import OAI.Analysis.LipschitzHilbert.Phase.SourcePhaseParameters

namespace OAI

/-! The marked prediction errors have a uniform total logarithmic budget
along an active path. The source cutoff is exactly `M = L^A_M`; the last
active index is included even when its drop crosses the cutoff. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
open PhaseCombinatorics

/-- Transfer from the fixed snapshot drop to the moving point, using the
factor two furnished by actual source path-drop comparability. -/
theorem source_error_of_drop_comparability {error ρ snapshotDrop pointDrop : ℝ}
    (hρ : 0 ≤ ρ) (hdrop : snapshotDrop/2 ≤ pointDrop)
    (herror : error ≤ ρ*snapshotDrop) : error ≤ (2*ρ)*pointDrop := by
  have h := mul_le_mul_of_nonneg_left hdrop hρ
  nlinarith

theorem stopped_source_error_transfer (n e snapshot : ℕ → ℝ)
    (count stop : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hdrop : ∀ j < stop, snapshot j/2 ≤ pathDrop n j)
    (he : ∀ j < count, e j ≤ if j < stop then ρ*snapshot j else 0) :
    ∀ j < count, e j ≤ if j < stop then (2*ρ)*pathDrop n j else 0 := by
  intro j hj
  by_cases hjs : j < stop
  · rw [ite_eq_left hjs]
    exact source_error_of_drop_comparability hρ (hdrop j hjs)
      (by simpa only [ite_eq_left hjs] using he j hj)
  · simpa only [ite_eq_right hjs] using he j hj

theorem eventually_source_drop_budget (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
      2*SourceParameters.step L^(-(1/32:ℝ))*(1+(C+4)*L) ≤ 1 := by
  have hsub := eventually_source_subpower_amplitude 2 (1/64) (by norm_num)
  filter_upwards [hsub,eventually_ge_atTop (max 1 (2*(C+5)))] with L hsub hlarge
  have hL : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hCL : 2*(C+5) ≤ L := (le_max_right _ _).trans hlarge
  have hb := hsub 1 1 (by norm_num) (by norm_num) (by simp; linarith)
  norm_num only [Real.one_rpow,Real.rpow_ofNat] at hb
  have hpoly : 2*(1+(C+4)*L) ≤ L^2 := by nlinarith
  have hpower : L^2 ≤ SourceParameters.step L^(1/64:ℝ) := by nlinarith [sq_nonneg L]
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  calc
    _ = (2*(1+(C+4)*L))*SourceParameters.step L^(-(1/32:ℝ)) := by ring
    _ ≤ SourceParameters.step L^(1/64:ℝ)*SourceParameters.step L^(-(1/32:ℝ)) :=
      mul_le_mul_of_nonneg_right (hpoly.trans hpower)
        (Real.rpow_nonneg (SourceParameters.step_pos L).le _)
    _ = SourceParameters.step L^(-(1/64:ℝ)) := by
      rw [← Real.rpow_add (SourceParameters.step_pos L)]
      norm_num
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num)

/-- The original mass bound `L^C N^2` gives the source active-drop estimate.
No lower bound on the initial mass is required when there are no active
indices. The terminal mass is allowed to be zero. -/
theorem eventually_source_stopped_error (C A_M : ℝ) (hC : 0 ≤ C) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop, ∀ (n e : ℕ → ℝ) (count stop : ℕ), stop ≤ count →
      ∀ N : ℝ, 0 < N → Real.log N ≤ 2*L → n 0 ≤ L^C*N^2 →
      (∀ j < stop, L^A_M < n j) → 0 ≤ n stop →
      (∀ j < count, e j ≤ if j < stop then
        (2*SourceParameters.step L^(-(1/32:ℝ)))*pathDrop n j else 0) →
      (∑ j ∈ Finset.range count, e j) ≤ 1 := by
  filter_upwards [eventually_source_drop_budget C hC,eventually_ge_atTop (1:ℝ)]
    with L hbudget hL
  intro n e count stop hstop N hN hlogN hmass hactive hlast he
  by_cases hs : stop = 0
  · have hz : (∑ j ∈ Finset.range count, e j) ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      simpa only [hs,Nat.not_lt_zero,ite_false] using he j (Finset.mem_range.mp hj)
    exact hz.trans zero_le_one
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hM : 1 ≤ L^A_M := Real.one_le_rpow hL hAM
  have hM0 : 0 < L^A_M := zero_lt_one.trans_le hM
  have hn : 0 < n 0 := hM0.trans (hactive 0 (Nat.pos_of_ne_zero hs))
  have hratio : 0 < n 0/L^A_M := div_pos hn hM0
  have hratioBound : n 0/L^A_M ≤ L^C*N^2 := (div_le_self hn.le hM).trans hmass
  have hlogL : Real.log L ≤ L := by
    have h := Real.log_le_sub_one_of_pos hL0
    linarith
  have hlog : Real.log (n 0/L^A_M) ≤ (C+4)*L := by
    calc
      _ ≤ Real.log (L^C*N^2) := Real.log_le_log hratio hratioBound
      _ = C*Real.log L+2*Real.log N := by
        rw [Real.log_mul (Real.rpow_pos_of_pos hL0 C).ne' (pow_pos hN 2).ne',
          Real.log_rpow hL0,Real.log_pow]
        ring
      _ ≤ C*L+2*(2*L) := add_le_add (mul_le_mul_of_nonneg_left hlogL hC)
        (mul_le_mul_of_nonneg_left hlogN (by norm_num))
      _ = (C+4)*L := by ring
  have hmaxlog : max 0 (Real.log (n 0/L^A_M)) ≤ (C+4)*L :=
    max_le (mul_nonneg (by linarith) hL0.le) hlog
  exact (stopped_error_budget n e count stop hstop hM0
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (SourceParameters.step_pos L).le _))
    hactive hlast hmaxlog he).trans hbudget

/-- Snapshot errors from the marked-cell comparison have total cost at most
one after the actual factor-two drop comparison. -/
theorem eventually_source_snapshot_stopped_error (C A_M : ℝ)
    (hC : 0 ≤ C) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop, ∀ (n e snapshot : ℕ → ℝ) (count stop : ℕ), stop ≤ count →
      ∀ N : ℝ, 0 < N → Real.log N ≤ 2*L → n 0 ≤ L^C*N^2 →
      (∀ j < stop, L^A_M < n j) → 0 ≤ n stop →
      (∀ j < stop, snapshot j/2 ≤ pathDrop n j) →
      (∀ j < count, e j ≤ if j < stop then
        SourceParameters.step L^(-(1/32:ℝ))*snapshot j else 0) →
      (∑ j ∈ Finset.range count, e j) ≤ 1 := by
  filter_upwards [eventually_source_stopped_error C A_M hC hAM] with L hL
  intro n e snapshot count stop hstop N hN hlogN hmass hactive hlast hdrop he
  exact hL n e count stop hstop N hN hlogN hmass hactive hlast
    (stopped_source_error_transfer n e snapshot count stop
      (Real.rpow_nonneg (SourceParameters.step_pos L).le _) hdrop he)

end LipschitzHilbert

end

end OAI
