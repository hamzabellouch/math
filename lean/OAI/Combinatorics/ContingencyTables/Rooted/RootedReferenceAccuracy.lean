import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhaseComposition
import OAI.Combinatorics.ContingencyTables.Counting.CompanionReferenceAccuracy

namespace OAI

/-! # Selected-root phase estimates have the required relative accuracy -/

namespace ContingencyTables.RootedReferenceAccuracy

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication RootedPhaseComposition RootedWarmStart
open CompanionReferenceAccuracy (tolerance relative_of_log_error)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem accurate_phases_relative (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (samples : ℕ → List (Set (Labels A×Bool))) (epsilon : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) (H : ℕ)
    (hall : ∀ j < H, Accurate A R samples (tolerance epsilon H) j) :
    (1-epsilon/4)*total A R H ≤ estimate A R samples H ∧
      estimate A R samples H ≤ (1+epsilon/4)*total A R H := by
  have hden : (0:ℝ) < 200*((H:ℝ)+1) := by positivity
  have heta : 0 ≤ tolerance epsilon H := by unfold tolerance; positivity
  have heta1 : tolerance epsilon H ≤ 1/4 := by
    unfold tolerance
    rw [div_le_iff₀ hden]
    nlinarith [show (0:ℝ) ≤ H by positivity]
  have hh := estimate_log_error A R samples (tolerance epsilon H) heta heta1 H hall
  have hC := total_positive A R H
  have herror : 4*(H:ℝ)*tolerance epsilon H ≤ epsilon/50 := by
    unfold tolerance
    rw [← mul_div_assoc,div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 50)]
    nlinarith [show (0:ℝ) ≤ H by positivity]
  have hr := relative_of_log_error epsilon (estimate A R samples H/total A R H) he0 he1
    (div_pos hh.1 hC) (hh.2.trans herror)
  constructor
  · exact (le_div_iff₀ hC).mp hr.1
  · exact (div_le_iff₀ hC).mp hr.2

/-- Once the separately proved terminal contamination estimate is
available, the successful actual phase history estimates the table count. -/
theorem reference_accuracy (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (samples : ℕ → List (Set (Labels A×Bool))) (epsilon Z : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) (hZ : 0 ≤ Z) (H : ℕ)
    (hall : ∀ j < H, Accurate A R samples (tolerance epsilon H) j)
    (hterminal : Z ≤ total A R H ∧ total A R H ≤ (1+epsilon/32)*Z) :
    (1-epsilon)*Z ≤ estimate A R samples H ∧ estimate A R samples H ≤ (1+epsilon)*Z := by
  apply final_estimate_accuracy epsilon Z (total A R H) (estimate A R samples H) he0 he1 hZ
  · refine ⟨hterminal.1, hterminal.2.trans ?_⟩
    nlinarith [mul_nonneg he0.le hZ]
  · exact accurate_phases_relative A R samples epsilon he0 he1 H hall

end ContingencyTables.RootedReferenceAccuracy

end OAI
