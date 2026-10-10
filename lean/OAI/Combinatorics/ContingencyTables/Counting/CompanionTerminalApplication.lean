import OAI.Combinatorics.ContingencyTables.Counting.CompanionTerminalMass
import OAI.Combinatorics.ContingencyTables.Counting.CompanionTerminalParameters
import OAI.Combinatorics.ContingencyTables.Counting.CompanionReferenceAccuracy

namespace OAI

/-! # The literal finite phase estimator has the required counting accuracy -/

namespace ContingencyTables.CompanionTerminalApplication

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionTerminalMass CompanionTerminalParameters
open CompanionPhaseComposition CompanionReferenceAccuracy CompanionAnnealing

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def finalPhase (A : Instance I J) (L : ℕ) (epsilon : ℝ) : ℕ :=
  10*coefficient L A.d epsilon*A.d^2*(A.W+1)

lemma final_parameter (A : Instance I J) (L : ℕ) (epsilon : ℝ) :
    (finalPhase A L epsilon:ℝ)/scale A=(coefficient L A.d epsilon:ℝ) := by
  have hs := (scale_positive A).ne'
  have hh : (finalPhase A L epsilon:ℝ)=(coefficient L A.d epsilon:ℝ)*scale A := by
    unfold finalPhase scale
    push_cast
    ring
  rw [hh,mul_div_cancel_right₀ _ hs]

theorem terminal_normalizer (A : Instance I J) (E : Endpoints A) (L : ℕ) (epsilon : ℝ)
    (he : 0 < epsilon) (he1 : epsilon < 1)
    (hW : 20*A.d ≤ A.W) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^L) :
    tableCount A ≤ total A (finalPhase A L epsilon) ∧
      total A (finalPhase A L epsilon) ≤ (1+epsilon/32)*tableCount A := by
  have hh := terminal_count_estimate A E (coefficient L A.d epsilon)
    (gamma L A.d epsilon) epsilon L (allowance L A.d epsilon)
    (by exact_mod_cast coefficient_positive L A.d epsilon A.hd he)
    (gamma_positive L A.d epsilon A.hd he) (gamma_le_one L A.d epsilon A.hd he1)
    he he1 (terminal_scale L A.d epsilon A.hd he)
    (near_fraction L A.d epsilon A.hd).le (far_fraction L A.d epsilon he)
    hW hL (allowance_bits L A.d epsilon) (allowance_positive L A.d epsilon)
  simpa only [total,weight,final_parameter] using hh

/-- Successful observations of the finite phase history
estimate the original bounded-table count, with terminal contamination
derived from the literal root/tree weights. -/
theorem successful_history_accuracy (A : Instance I J) (E : Endpoints A)
    (samples : ℕ → List (Set (Labels A×Bool))) (L : ℕ) (epsilon : ℝ)
    (he : 0 < epsilon) (he1 : epsilon < 1)
    (hW : 20*A.d ≤ A.W) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^L)
    (hall : ∀ j < finalPhase A L epsilon,
      Accurate A samples (tolerance epsilon (finalPhase A L epsilon)) j) :
    (1-epsilon)*tableCount A ≤ estimate A samples (finalPhase A L epsilon) ∧
      estimate A samples (finalPhase A L epsilon) ≤ (1+epsilon)*tableCount A := by
  exact reference_accuracy A samples epsilon (tableCount A) he he1
    (by linarith [tableCount_ge_one A]) (finalPhase A L epsilon) hall
    (terminal_normalizer A E L epsilon he he1 hW hL)

end ContingencyTables.CompanionTerminalApplication

end OAI
