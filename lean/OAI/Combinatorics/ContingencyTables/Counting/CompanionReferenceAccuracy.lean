import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseComposition

namespace OAI

/-! # Relative accuracy of the literal companion ratio estimator

The source's tolerance epsilon/(200(H+1)) turns the proved accumulated
logarithmic error into the required multiplicative error. The terminal
contamination bound supplies the remaining error term.
-/

namespace ContingencyTables.CompanionReferenceAccuracy

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication CompanionPhaseComposition

theorem relative_of_log_error (epsilon R : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (hR : 0 < R) (herr : |Real.log R| ≤ epsilon/50) :
    1-epsilon/4 ≤ R ∧ R ≤ 1+epsilon/4 := by
  have hl := Real.log_le_sub_one_of_pos hR
  have hu := Real.one_sub_inv_le_log_of_pos hR
  have he := abs_le.mp herr
  have hinv : 1-epsilon/50 ≤ R⁻¹ := by linarith
  have hm := mul_le_mul_of_nonneg_right hinv hR.le
  rw [inv_mul_cancel₀ hR.ne'] at hm
  have hc : (1-epsilon/50)*(1+epsilon/4) ≥ 1 := by
    nlinarith [mul_nonneg he0.le (sub_nonneg.mpr he1.le)]
  constructor
  · linarith
  · exact le_of_mul_le_mul_left (hm.trans hc) (show 0 < 1-epsilon/50 by linarith)

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def tolerance (epsilon : ℝ) (H : ℕ) : ℝ :=
  epsilon/(200*((H:ℝ)+1))

theorem accurate_phases_relative (A : Instance I J)
    (samples : ℕ → List (Set (Labels A×Bool))) (epsilon : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) (H : ℕ)
    (hall : ∀ j < H, Accurate A samples (tolerance epsilon H) j) :
    (1-epsilon/4)*total A H ≤ estimate A samples H ∧
      estimate A samples H ≤ (1+epsilon/4)*total A H := by
  have hden : (0:ℝ) < 200*((H:ℝ)+1) := by positivity
  have heta : 0 ≤ tolerance epsilon H := by unfold tolerance; positivity
  have heta1 : tolerance epsilon H ≤ 1/4 := by
    unfold tolerance
    rw [div_le_iff₀ hden]
    nlinarith [show (0:ℝ) ≤ H by positivity]
  have hh := estimate_log_error A samples (tolerance epsilon H) heta heta1 H hall
  have hC := total_positive A H
  have herror : 4*(H:ℝ)*tolerance epsilon H ≤ epsilon/50 := by
    unfold tolerance
    rw [← mul_div_assoc,div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 50)]
    nlinarith [show (0:ℝ) ≤ H by positivity]
  have hr := relative_of_log_error epsilon (estimate A samples H/total A H) he0 he1
    (div_pos hh.1 hC) (hh.2.trans herror)
  constructor
  · exact (le_div_iff₀ hC).mp hr.1
  · exact (div_le_iff₀ hC).mp hr.2

/-- The terminal contamination bound and a successful phase history
give a relative-error estimate of the table count. -/
theorem reference_accuracy (A : Instance I J)
    (samples : ℕ → List (Set (Labels A×Bool))) (epsilon Z : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) (hZ : 0 ≤ Z) (H : ℕ)
    (hall : ∀ j < H, Accurate A samples (tolerance epsilon H) j)
    (hterminal : Z ≤ total A H ∧ total A H ≤ (1+epsilon/32)*Z) :
    (1-epsilon)*Z ≤ estimate A samples H ∧ estimate A samples H ≤ (1+epsilon)*Z := by
  apply final_estimate_accuracy epsilon Z (total A H) (estimate A samples H) he0 he1 hZ
  · refine ⟨hterminal.1, hterminal.2.trans ?_⟩
    nlinarith [mul_nonneg he0.le hZ]
  · exact accurate_phases_relative A samples epsilon he0 he1 H hall

end ContingencyTables.CompanionReferenceAccuracy

end OAI
