import OAI.Combinatorics.ContingencyTables.Rooted.RootedTerminalMass
import OAI.Combinatorics.ContingencyTables.Rooted.RootedReferenceAccuracy
import OAI.Combinatorics.ContingencyTables.Counting.CompanionTerminalApplication

namespace OAI

/-! # Actual selected-root terminal counts and successful phase histories -/

namespace ContingencyTables.RootedTerminalApplication

open scoped BigOperators Classical
open CompanionFactorialApplication RootedTerminalMass CompanionTerminalParameters
open RootedPhaseComposition RootedReferenceAccuracy RootedAnnealing RootedWarmStart
open CompanionReferenceAccuracy (tolerance)
open CompanionTerminalMass (Endpoints tableCount tableCount_ge_one)
open CompanionTerminalApplication (finalPhase final_parameter)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem terminal_normalizer (A : Instance I J) (R : RootedCompletion.Selection A.T) (E : Endpoints A) (L : ℕ) (epsilon : ℝ)
    (he : 0 < epsilon) (he1 : epsilon < 1)
    (hW : 20*A.d ≤ A.W) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^L) :
    tableCount A ≤ total A R (finalPhase A L epsilon) ∧
      total A R (finalPhase A L epsilon) ≤ (1+epsilon/32)*tableCount A := by
  have hh := terminal_count_estimate A R E (coefficient L A.d epsilon)
    (gamma L A.d epsilon) epsilon L (allowance L A.d epsilon)
    (by exact_mod_cast coefficient_positive L A.d epsilon A.hd he)
    (gamma_positive L A.d epsilon A.hd he) (gamma_le_one L A.d epsilon A.hd he1)
    he he1 (terminal_scale L A.d epsilon A.hd he)
    (near_fraction L A.d epsilon A.hd).le (far_fraction L A.d epsilon he)
    hW hL (allowance_bits L A.d epsilon) (allowance_positive L A.d epsilon)
  simpa only [total,weight,final_parameter] using hh

/-- Successful observations of the original finite phase history
estimate the original bounded-table count, with terminal contamination
derived from the literal root/tree weights. -/
theorem successful_history_accuracy (A : Instance I J) (R : RootedCompletion.Selection A.T) (E : Endpoints A)
    (samples : ℕ → List (Set (Labels A×Bool))) (L : ℕ) (epsilon : ℝ)
    (he : 0 < epsilon) (he1 : epsilon < 1)
    (hW : 20*A.d ≤ A.W) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^L)
    (hall : ∀ j < finalPhase A L epsilon,
      Accurate A R samples (tolerance epsilon (finalPhase A L epsilon)) j) :
    (1-epsilon)*tableCount A ≤ estimate A R samples (finalPhase A L epsilon) ∧
      estimate A R samples (finalPhase A L epsilon) ≤ (1+epsilon)*tableCount A := by
  exact reference_accuracy A R samples epsilon (tableCount A) he he1
    (by linarith [tableCount_ge_one A]) (finalPhase A L epsilon) hall
    (terminal_normalizer A R E L epsilon he he1 hW hL)

end ContingencyTables.RootedTerminalApplication

end OAI
