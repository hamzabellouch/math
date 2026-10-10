import OAI.Combinatorics.ContingencyTables.Counting.CountingPublicInputBounds
import OAI.Combinatorics.ContingencyTables.Counting.CountingLabelCountProgram
import OAI.Combinatorics.ContingencyTables.Counting.CountingPhaseScalarProgram
import OAI.Combinatorics.ContingencyTables.Machines.ScalarScheduleBounds

namespace OAI

/-! # Public polynomial bounds for the terminal grid and phase controls -/

namespace ContingencyTables.CountingPublicTerminalBounds
open CountingTerminalBounds CountingPublicInputBounds CompanionFactorialApplication
open ScalarScheduleProgram Polynomial
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma coefficient_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    ComputedCountingParameters.coefficient r c b epsilon ≤
      coefficientPolynomial.eval (size r c b epsilon delta) :=
  coefficient_bound _ _ (size r c b epsilon delta) _ epsilon he (inverse_le r c b epsilon delta)
    (capacityBits_le hEK r c b hne epsilon delta) (dimension_le r c b epsilon delta) (le_refl _)

lemma terminal_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    ComputedCountingParameters.binCount r c b epsilon ≤ gridPolynomial.eval (size r c b epsilon delta) ∧
    ComputedCountingParameters.cutoff r c b epsilon ≤ cutoffPolynomial.eval (size r c b epsilon delta) ∧
    ComputedCountingParameters.phases r c b epsilon ≤ phasePolynomial.eval (size r c b epsilon delta) :=
  terminal_bounds _ _ _ _ _ (coefficient_public hEK r c b hne epsilon delta he)
    (dimension_le r c b epsilon delta) rfl rfl

lemma label_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) ≤
      (size r c b epsilon delta)*cutoffPolynomial.eval (size r c b epsilon delta) := by
  have hl := CountingLabelCountProgram.count_bound (ComputedCountingParameters.data hEK r c b hne epsilon he)
  exact hl.trans (Nat.mul_le_mul (dimension_le r c b epsilon delta)
    (terminal_public hEK r c b hne epsilon delta he).2.1)

def basicPolynomial : Polynomial ℕ := X*cutoffPolynomial+cutoffPolynomial+phasePolynomial+X+1

def restartPolynomial : Polynomial ℕ := CountingPhaseScalarProgram.restartTime.bound.comp basicPolynomial

lemma scalar_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let H := ComputedCountingParameters.phases r c b epsilon
    let L := ComputedCountingParameters.capacityBits r c b
    ∀ x∈[Fintype.card (Labels A),A.W,H,0,0,0,L],
      x ≤ basicPolynomial.eval (size r c b epsilon delta) := by
  dsimp only
  have hp := label_public hEK r c b hne epsilon delta he
  have hw := (terminal_public hEK r c b hne epsilon delta he).2.1
  have hh := (terminal_public hEK r c b hne epsilon delta he).2.2
  have hl := capacityBits_le hEK r c b hne epsilon delta
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  simp only [basicPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one]
  change x=Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) ∨
    x=ComputedCountingParameters.cutoff r c b epsilon ∨
    x=ComputedCountingParameters.phases r c b epsilon ∨ x=0 ∨ x=0 ∨ x=0 ∨
    x=ComputedCountingParameters.capacityBits r c b at hx
  omega

lemma restart_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    CompanionTargetMixing.restartTime A (ComputedCountingParameters.phases r c b epsilon)
      (ComputedCountingParameters.capacityBits r c b) ≤ restartPolynomial.eval (size r c b epsilon delta) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let H := ComputedCountingParameters.phases r c b epsilon
  let L := ComputedCountingParameters.capacityBits r c b
  have hb := CountingPhaseScalarProgram.restartTime.eval_le_of_mem
    [Fintype.card (Labels A),A.W,H,0,0,0,L]
    (basicPolynomial.eval (size r c b epsilon delta))
    (scalar_public hEK r c b hne epsilon delta he)
  rw [CountingPhaseScalarProgram.restartTime_instance A H L 0 0 0] at hb
  simpa only [restartPolynomial,Polynomial.eval_comp] using hb

end
end ContingencyTables.CountingPublicTerminalBounds

end OAI
