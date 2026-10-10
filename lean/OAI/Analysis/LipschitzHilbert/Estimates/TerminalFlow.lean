import OAI.Analysis.LipschitzHilbert.Trees.HierarchyVariation

namespace OAI

/-! Conservation and good-terminal domination for finite stopped path flows. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable (κ ι : Type*) [Fintype κ] [Fintype ι]

/-- A finite path flow with a unique final edge for each terminal top.
The balance law includes both continuing and terminating mass. -/
structure TerminalFlow (N : ℕ) where
  occupancy : ℕ → κ → ℝ
  exitLevel : ι → ℕ
  exitNode : ι → κ
  exitRate : ι → ℝ
  nonnegative : ∀ j ≤ N, ∀ v, 0 ≤ occupancy j v
  rate_nonnegative : ∀ i, 0 ≤ exitRate i
  exit_before : ∀ i, exitLevel i < N
  initial_total : ∑ v, occupancy 0 v = 1
  final_total : ∑ v, occupancy N v = 0
  balance : ∀ j < N,
    (∑ v, occupancy (j + 1) v) +
      (∑ i, if exitLevel i = j then occupancy j (exitNode i) * exitRate i else 0) =
        ∑ v, occupancy j v

variable {κ ι}

namespace TerminalFlow

variable {N : ℕ} (F : TerminalFlow κ ι N)

def terminalProbability (i : ι) : ℝ :=
  F.occupancy (F.exitLevel i) (F.exitNode i) * F.exitRate i

theorem terminalProbability_nonnegative (i : ι) : 0 ≤ F.terminalProbability i :=
  mul_nonneg (F.nonnegative _ (F.exit_before i).le _) (F.rate_nonnegative i)

theorem exiting_nonnegative (j : ℕ) (hj : j < N) :
    0 ≤ ∑ i, if F.exitLevel i = j then F.occupancy j (F.exitNode i) * F.exitRate i else 0 := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact mul_nonneg (F.nonnegative j hj.le _) (F.rate_nonnegative i)
  · rfl

theorem occupancy_total_le_one : ∀ j ≤ N, (∑ v, F.occupancy j v) ≤ 1 := by
  intro j hj
  induction j with
  | zero => exact F.initial_total.le
  | succ j ih =>
    have hjN : j < N := by omega
    have hbalance := F.balance j hjN
    have hnonnegative := F.exiting_nonnegative j hjN
    have hprev := ih (by omega)
    linarith

theorem occupancy_le_one (j : ℕ) (hj : j ≤ N) (v : κ) : F.occupancy j v ≤ 1 := by
  exact (Finset.single_le_sum (fun k _ => F.nonnegative j hj k) (Finset.mem_univ v)).trans
    (F.occupancy_total_le_one j hj)

theorem terminalProbability_le_rate (i : ι) : F.terminalProbability i ≤ F.exitRate i := by
  exact mul_le_of_le_one_left (F.rate_nonnegative i)
    (F.occupancy_le_one _ (F.exit_before i).le _)

theorem terminalProbability_total : ∑ i, F.terminalProbability i = 1 := by
  classical
  have htime (i : ι) :
      (∑ j ∈ Finset.range N,
        if F.exitLevel i = j then F.occupancy j (F.exitNode i) * F.exitRate i else 0) =
          F.terminalProbability i := by
    rw [Finset.sum_eq_single (F.exitLevel i)]
    · simp [terminalProbability]
    · intro j _ hj
      simp [Ne.symm hj]
    · intro hi
      exact False.elim (hi (Finset.mem_range.mpr (F.exit_before i)))
  calc
    _ = ∑ i, ∑ j ∈ Finset.range N,
        if F.exitLevel i = j then F.occupancy j (F.exitNode i) * F.exitRate i else 0 := by
      simp_rw [htime]
    _ = ∑ j ∈ Finset.range N, ∑ i,
        if F.exitLevel i = j then F.occupancy j (F.exitNode i) * F.exitRate i else 0 :=
      Finset.sum_comm
    _ = ∑ j ∈ Finset.range N, ((∑ v, F.occupancy j v) - ∑ v, F.occupancy (j + 1) v) := by
      apply Finset.sum_congr rfl
      intro j hj
      linarith [F.balance j (Finset.mem_range.mp hj)]
    _ = (∑ v, F.occupancy 0 v) - ∑ v, F.occupancy N v :=
      Finset.sum_range_sub' _ N
    _ = 1 := by rw [F.initial_total, F.final_total]; norm_num

theorem bad_terminal_probability_le (bad : Finset ι) (h : ι → ℝ) (C : ℝ)
    (hrate : ∀ i, F.exitRate i ≤ C * h i) :
    (∑ i ∈ bad, F.terminalProbability i) ≤ C * ∑ i ∈ bad, h i := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => (F.terminalProbability_le_rate i).trans (hrate i))

theorem good_terminal_probability_half [DecidableEq ι] (bad : Finset ι) (h : ι → ℝ) (C : ℝ)
    (hrate : ∀ i, F.exitRate i ≤ C * h i) (hsmall : C * ∑ i ∈ bad, h i ≤ 1 / 2) :
    1 / 2 ≤ ∑ i ∈ Finset.univ \ bad, F.terminalProbability i := by
  have hbad := (F.bad_terminal_probability_le bad h C hrate).trans hsmall
  have hsum := Finset.sum_sdiff (Finset.subset_univ bad)
    (f := F.terminalProbability)
  rw [F.terminalProbability_total] at hsum
  linarith

end TerminalFlow

end LipschitzHilbert

end

end OAI
