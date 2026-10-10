import Mathlib
import OAI.Combinatorics.UniformKServer.CoarseData
import OAI.Combinatorics.UniformKServer.SyntheticCore

namespace OAI

                                   
section

/-! Pointwise held-size/core bridges for the actual persistent rank trackers. -/
noncomputable section
namespace UniformKServer.CoarseBridge
open Finset UniformKServer.CoarseData UniformKServer.RankData
open scoped Classical
variable {Ω R : Type*} [Fintype Ω] [Fintype R]

theorem held_some (I : R → RankTracking.Input Ω) (t : ℕ) (ω : Ω) {b : ℝ}
    (hb : activeState I t ω=some b) : heldSize I t ω=b := by
  simp only [heldSize,hb,AllocationSchedule.size]

theorem held_none (I : R → RankTracking.Input Ω) (t : ℕ) (ω : Ω)
    (hb : activeState I t ω=none) : heldSize I t ω=0 := by
  simp only [heldSize,hb,AllocationSchedule.size]

theorem held_bound (I : R → RankTracking.Input Ω) (t : ℕ) (ω : Ω) :
    heldSize I t ω ≤ (11/10)*totalSize (fun r => (I r).posterior t ω) := by
  cases hb : activeState I t ω with
  | none =>
    rw [held_none I t ω hb]
    exact mul_nonneg (by norm_num) (sum_nonneg fun r _ => sizeRank_nonneg _)
  | some b => rw [held_some I t ω hb]; exact (active_accuracy I t ω hb).2.1

theorem held_min (I : R → RankTracking.Input Ω) (t : ℕ) (ω : Ω)
    (hp : 0 < heldSize I t ω) : (9/100000:ℝ) ≤ heldSize I t ω := by
  cases hb : activeState I t ω with
  | none => rw [held_none I t ω hb] at hp; exact (lt_irrefl _ hp).elim
  | some b =>
    rw [held_some I t ω hb]
    have ha := active_accuracy I t ω hb
    norm_num [cutoff] at ha
    linarith

theorem inactive_flags (I : R → RankTracking.Input Ω) (t : ℕ) (ω : Ω)
    (hb : activeState I t ω=none) (r : R) : core (I r) t ω=false := by
  have hz := (inactive_zero I t ω 3 hb).1
  have h : (if core (I r) t ω then (1:ℝ) else 0) ≤ coreCount (fun j => core (I j) t ω) :=
    single_le_sum (f:=fun j => if core (I j) t ω then (1:ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) (mem_univ r)
  rw [hz] at h
  cases hf : core (I r) t ω
  · rfl
  · simp only [hf,ite_true] at h
    norm_num at h

theorem held_zero_flags (I : R → RankTracking.Input Ω) (t : ℕ) (ω : Ω)
    (hz : heldSize I t ω=0) (r : R) : core (I r) t ω=false := by
  cases hb : activeState I t ω with
  | none => exact inactive_flags I t ω hb r
  | some b =>
    have ha := active_accuracy I t ω hb
    rw [held_some I t ω hb] at hz
    norm_num [cutoff] at ha
    exfalso
    nlinarith [ha.1,ha.2.2]

theorem core_count_bound (I : R → RankTracking.Input Ω) (t : ℕ) (ω : Ω) :
    coreCount (fun r => core (I r) t ω) ≤ 40*heldSize I t ω := by
  cases hb : activeState I t ω with
  | none =>
    rw [(inactive_zero I t ω 3 hb).1,held_none I t ω hb,mul_zero]
  | some b =>
    have hd := core_flex_domination (fun r => core (I r) t ω) 3
      (fun r => (I r).posterior t ω) (by norm_num [RankFunctions.allowed])
      (fun r => ((I r).posterior_range t ω).1) (fun r hr => by
        have hh := core_small (I r) t ω hr
        norm_num [RankFunctions.pstar] at hh ⊢
        linarith)
    have hf : 0 ≤ flex (fun r => core (I r) t ω) 3 (fun r => (I r).posterior t ω) := by
      apply sum_nonneg
      intro r _
      split_ifs
      · exact le_rfl
      · exact RankFunctions.rank_nonneg (by norm_num [RankFunctions.allowed])
    have ha := (active_accuracy I t ω hb).1
    rw [held_some I t ω hb]
    linarith

theorem core_input_bound (I : R → RankTracking.Input Ω) (t : ℕ) (ω : Ω) :
    SyntheticCore.input (fun r => (I r).posterior t ω) (fun r => core (I r) t ω) ≤ 40*heldSize I t ω :=
  (core_mass_bounds (fun r => core (I r) t ω) (fun r => (I r).posterior t ω)
    (fun r => (I r).posterior_range t ω)).2.trans (core_count_bound I t ω)

end UniformKServer.CoarseBridge

end


end

end OAI
