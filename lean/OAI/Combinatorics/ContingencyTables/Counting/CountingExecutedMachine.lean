import OAI.Combinatorics.ContingencyTables.Counting.CountingPositiveWordBound
import OAI.Combinatorics.ContingencyTables.Counting.CountingBranchMachine
import OAI.Combinatorics.ContingencyTables.Counting.CountingMachineTime

namespace OAI

/-! # One fixed counting machine with the computed adaptive program -/
namespace ContingencyTables.CountingExecutedMachine
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open scoped Classical
noncomputable section

abbrev positive := CountingAmplifiedProgram.output CountingPositiveProgram.output CountingPositiveProgram.bitCount
abbrev positiveWidth := CountingAmplifiedProgram.budget CountingPositiveProgram.bitCount

def positiveRealizer : Realizer positive := CountingAmplifiedProgram.outputRealizer
  CountingPositiveProgram.output CountingPositiveProgram.outputRealizer
  CountingPositiveProgram.bitCount CountingPositiveProgram.bitCountRealizer

def positiveWidthRealizer : Realizer positiveWidth := CountingAmplifiedProgram.budgetRealizer
  CountingPositiveProgram.bitCount CountingPositiveProgram.bitCountRealizer

lemma polynomial_positive : PolynomialTime positiveRealizer :=
  CountingAmplifiedProgram.polynomial_output CountingPositiveProgram.output
    CountingPositiveProgram.outputRealizer CountingPositiveProgram.bitCount
    CountingPositiveProgram.bitCountRealizer CountingPositiveProgram.polynomial_output
    CountingPositiveProgram.polynomial_bitCount

lemma polynomial_positiveWidth : PolynomialTime positiveWidthRealizer :=
  CountingAmplifiedProgram.polynomial_budget CountingPositiveProgram.bitCount
    CountingPositiveProgram.bitCountRealizer CountingPositiveProgram.polynomial_bitCount

def machine : RandomMachine :=
  CountingBranchProgram.machine positive positiveRealizer positiveWidth positiveWidthRealizer

def machineTime (as : List Symbol) : ℕ :=
  CountingBranchProgram.machineTime positive positiveRealizer positiveWidth positiveWidthRealizer as

abbrev wordCount := CountingBranchProgram.publicBudget positiveWidth
abbrev publicOutput := CountingBranchProgram.publicOutput positive
abbrev sourceValue := CountingBranchProgram.sourceValue positive positiveWidth

theorem public_time (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1) :
    ∃ C d : ℕ,0<C ∧ ∀ (m n : ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
      (epsilon delta : ℚ),0<epsilon→0<delta→
      machineTime (Algorithms.encodeCountingInput r c b epsilon delta) ≤
        Algorithms.countingTime C d r c b epsilon delta := by
  exact CountingMachineTime.public_bound
    (CountingBranchProgram.publicBudgetRealizer positiveWidth positiveWidthRealizer)
    (CountingBranchProgram.publicOutputRealizer positive positiveRealizer)
    (CountingBranchProgram.polynomial_publicBudget positiveWidth positiveWidthRealizer polynomial_positiveWidth)
    (CountingBranchProgram.polynomial_publicOutput positive positiveRealizer polynomial_positive)
    (CountingBranchProgram.budgetPolynomial CountingPositiveWordBound.amplifiedPolynomial)
    (CountingPositiveWordBound.branch_public hEK)

variable {m n : ℕ}

theorem outputs_nonnegative (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (t : ℕ)
    (ht : machineTime (Algorithms.encodeCountingInput r c b epsilon delta)≤t) :
    ∀ bits : Bits t,∃ q : ℚ,0≤q ∧
      Outputs machine (Algorithms.encodeCountingInput r c b epsilon delta) bits q :=
  CountingBranchProgram.outputs_nonnegative positive positiveRealizer positiveWidth positiveWidthRealizer
    r c b epsilon delta t ht

theorem outputs_zero (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ)
    (hz : Algorithms.count r c b=0) (t : ℕ)
    (ht : machineTime (Algorithms.encodeCountingInput r c b epsilon delta)≤t) :
    ∀ bits : Bits t,Outputs machine (Algorithms.encodeCountingInput r c b epsilon delta) bits 0 :=
  CountingBranchProgram.outputs_zero positive positiveRealizer positiveWidth positiveWidthRealizer
    hEK r c b epsilon delta hz t ht

end
end ContingencyTables.CountingExecutedMachine

end OAI
