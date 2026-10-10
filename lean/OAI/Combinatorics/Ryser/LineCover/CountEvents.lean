import OAI.Combinatorics.Ryser.LineCover.MeanCounts
import OAI.Combinatorics.Ryser.LineCover.CountConcentration
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover.DeletionProcess

variable {F : Type*} [Field F] [Fintype F] [instDecidableEqF : DecidableEq F]
  {D : ℕ} {δ : ℝ} (process : DeletionProcess F D δ)

private theorem fieldCard_pos_real : 0 < (Fintype.card F : ℝ) := let _ := instDecidableEqF; by
  exact_mod_cast Fintype.card_pos (α := F)

theorem total_count_concentration (hD : 0 < D) (u : ℝ) (hu : 0 < u) :
    process.law.prob (fun ω => u ≤
        |retainedCount ∅ Finset.univ ω -
          process.survival * (Fintype.card F : ℝ) ^ 2|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) *
        min (u ^ 2 / (4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ) ^ 3))
          (u / (2 * (D : ℝ) ^ 2 * (Fintype.card F : ℝ)))) := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hq := fieldCard_pos_real (F := F)
  have hn : (process.trialsCount : ℝ) ≤ (D : ℝ) * (Fintype.card F : ℝ) := by
    exact_mod_cast process.trialsCount_le
  have hC : 2 * (D : ℝ) * ((D * Fintype.card F : ℕ) : ℝ) =
      2 * (D : ℝ) ^ 2 * (Fintype.card F : ℝ) := by
    rw [Nat.cast_mul]
    ring
  have hV : (process.trialsCount : ℝ) *
      (2 * (D : ℝ) * ((D * Fintype.card F : ℕ) : ℝ)) ^ 2 ≤
        4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ) ^ 3 := by
    rw [hC]
    calc
      _ ≤ ((D : ℝ) * (Fintype.card F : ℝ)) *
          (2 * (D : ℝ) ^ 2 * (Fintype.card F : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hn (sq_nonneg _)
      _ = _ := by ring
  have h := retainedCount_coordinate_concentration process.trials ∅ Finset.univ
    (D * Fintype.card F)
    (fun S hS _ => by simpa using process.shapeSize S hS)
    (2 * (D : ℝ) ^ 2 * (Fintype.card F : ℝ))
    (4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ) ^ 3) u
    (by positivity) (by positivity) hu hC.le hV
  change process.law.prob (fun ω => u ≤
      |retainedCount ∅ Finset.univ ω -
        process.law.expectation (retainedCount ∅ Finset.univ)|) ≤ _ at h
  rw [process.expectation_totalCount] at h
  exact h

theorem ignored_line_count_concentration (hD : 0 < D) (l : AffineLine F)
    (u : ℝ) (hu : 0 < u) :
    process.law.prob (fun ω => u ≤
        |retainedCount {linePoints l} (linePoints l) ω -
          process.law.expectation (retainedCount {linePoints l} (linePoints l))|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) *
        min (u ^ 2 / (4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ)))
          (u / (2 * (D : ℝ) ^ 2))) := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hq := fieldCard_pos_real (F := F)
  have hn : (process.trialsCount : ℝ) ≤ (D : ℝ) * (Fintype.card F : ℝ) := by
    exact_mod_cast process.trialsCount_le
  have hC : 2 * (D : ℝ) * (D : ℝ) = 2 * (D : ℝ) ^ 2 := by ring
  have hV : (process.trialsCount : ℝ) * (2 * (D : ℝ) * (D : ℝ)) ^ 2 ≤
      4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ) := by
    calc
      _ ≤ ((D : ℝ) * (Fintype.card F : ℝ)) *
          (2 * (D : ℝ) * (D : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hn (sq_nonneg _)
      _ = _ := by ring
  exact retainedCount_coordinate_concentration process.trials {linePoints l}
    (linePoints l) D
    (fun S hS hnot => process.sparse S hS l (by simpa using hnot))
    (2 * (D : ℝ) ^ 2) (4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ)) u
    (by positivity) (by positivity) hu hC.le hV

theorem ignored_line_lower_tail (hD : 0 < D) (hδ : 0 < δ) (l : AffineLine F) :
    process.law.prob (fun ω =>
        retainedCount {linePoints l} (linePoints l) ω <
          δ * (Fintype.card F : ℝ) / 2) ≤
      2 * Real.exp (-(1 / 4 : ℝ) *
        min ((δ * (Fintype.card F : ℝ) / 2) ^ 2 /
          (4 * (D : ℝ) ^ 5 * (Fintype.card F : ℝ)))
          ((δ * (Fintype.card F : ℝ) / 2) / (2 * (D : ℝ) ^ 2))) := by
  have hq := fieldCard_pos_real (F := F)
  have hδq : δ * (Fintype.card F : ℝ) ≤
      process.survival * (Fintype.card F : ℝ) :=
    mul_le_mul_of_nonneg_right process.survivalLower hq.le
  have hmean : 2 * (δ * (Fintype.card F : ℝ) / 2) ≤
      process.law.expectation (retainedCount {linePoints l} (linePoints l)) := by
    have hlo := (process.expectation_ignored_lineCount_bounds l).1
    linarith
  exact (prob_lt_le_prob_centered process.law
    (retainedCount {linePoints l} (linePoints l))
    (δ * (Fintype.card F : ℝ) / 2) hmean).trans
      (process.ignored_line_count_concentration hD l
        (δ * (Fintype.card F : ℝ) / 2) (by positivity))

end RyserCoveringCounterexample.LineCover.DeletionProcess

end

end OAI
