import OAI.Analysis.CircleDomains.Topology.FiniteCompactTests
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Finite positive tolerances give an explicit summable error budget.
Each later step respects every earlier saved tolerance. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def savedToleranceMinimum (ε : ℝ) : List ℝ → ℝ
  | [] => min 1 ε
  | t :: ts => min t (savedToleranceMinimum ε ts)

 theorem savedToleranceMinimum_pos {ε : ℝ} (hε : 0 < ε) {ts : List ℝ}
    (hts : ∀ t ∈ ts, 0 < t) : 0 < savedToleranceMinimum ε ts := by
  induction ts with
  | nil => exact lt_min zero_lt_one hε
  | cons t ts ih =>
    exact lt_min (hts t (List.mem_cons_self)) (ih (fun x hx => hts x (List.mem_cons_of_mem t hx)))

 theorem savedToleranceMinimum_le {ε t : ℝ} {ts : List ℝ} (ht : t ∈ ts) :
    savedToleranceMinimum ε ts ≤ t := by
  induction ts with
  | nil => simp at ht
  | cons s ts ih =>
    rcases List.mem_cons.mp ht with rfl | ht
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih ht)

 theorem savedToleranceMinimum_le_initial (ε : ℝ) (ts : List ℝ) :
    savedToleranceMinimum ε ts ≤ min 1 ε := by
  induction ts with
  | nil => exact le_rfl
  | cons t ts ih => exact (min_le_right _ _).trans ih

 def recursiveTestBudget (ε : ℝ) (n : ℕ) (ts : List ℝ) : ℝ :=
  (1/2 : ℝ)^(n+3)*savedToleranceMinimum ε ts

 theorem recursiveTestBudget_pos {ε : ℝ} (hε : 0 < ε) (n : ℕ) {ts : List ℝ}
    (hts : ∀ t ∈ ts, 0 < t) : 0 < recursiveTestBudget ε n ts := by
  exact mul_pos (pow_pos (by norm_num) _) (savedToleranceMinimum_pos hε hts)

 theorem recursiveTestBudget_le_saved {ε t : ℝ} (n : ℕ) {ts : List ℝ} (ht : t ∈ ts) :
    recursiveTestBudget ε n ts ≤ (1/2 : ℝ)^(n+3)*t :=
  mul_le_mul_of_nonneg_left (savedToleranceMinimum_le ht) (by positivity)

 theorem recursiveTestBudget_le_initial (ε : ℝ) (n : ℕ) (ts : List ℝ) :
    recursiveTestBudget ε n ts ≤ (1/2 : ℝ)^(n+3)*ε := by
  exact mul_le_mul_of_nonneg_left
    ((savedToleranceMinimum_le_initial ε ts).trans (min_le_right _ _)) (by positivity)

end CircleDomainRigidity

end

end OAI
