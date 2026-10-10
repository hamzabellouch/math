import OAI.Computability.BinPacking.Computation.MachineUnaryLessAt
import OAI.Computability.BinPacking.CookLevin.ConfigIndex

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.Bounds

open Polynomial

noncomputable def pairLengthPolynomial (q : Polynomial ℕ) : Polynomial ℕ :=
  C 2 * X + q + 1

noncomputable def horizonPolynomial (p q : Polynomial ℕ) : Polynomial ℕ :=
  p.comp (pairLengthPolynomial q)

noncomputable def capacityPolynomial (p q : Polynomial ℕ) (pushes : ℕ) : Polynomial ℕ :=
  pairLengthPolynomial q + C pushes * horizonPolynomial p q

@[simp] theorem pairLengthPolynomial_eval (q : Polynomial ℕ) (n : ℕ) :
    (pairLengthPolynomial q).eval n = 2 * n + q.eval n + 1 := by
  simp [pairLengthPolynomial]

@[simp] theorem horizonPolynomial_eval (p q : Polynomial ℕ) (n : ℕ) :
    (horizonPolynomial p q).eval n = p.eval (2 * n + q.eval n + 1) := by
  simp [horizonPolynomial, Polynomial.eval_comp]

@[simp] theorem capacityPolynomial_eval (p q : Polynomial ℕ) (pushes n : ℕ) :
    (capacityPolynomial p q pushes).eval n =
      2 * n + q.eval n + 1 + pushes * p.eval (2 * n + q.eval n + 1) := by
  simp [capacityPolynomial]

theorem paired_length_le (q : Polynomial ℕ) (n witnessLength : ℕ)
    (hw : witnessLength ≤ q.eval n) :
    2 * n + witnessLength + 1 ≤ (pairLengthPolynomial q).eval n := by
  rw [pairLengthPolynomial_eval]
  omega

theorem one_le_pairLength (q : Polynomial ℕ) (n : ℕ) :
    1 ≤ (pairLengthPolynomial q).eval n := by
  rw [pairLengthPolynomial_eval]
  omega

theorem pairLength_le_capacity (p q : Polynomial ℕ) (pushes n : ℕ) :
    (pairLengthPolynomial q).eval n ≤ (capacityPolynomial p q pushes).eval n := by
  simp only [capacityPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  exact Nat.le_add_right _ _

theorem one_le_capacity (p q : Polynomial ℕ) (pushes n : ℕ) :
    1 ≤ (capacityPolynomial p q pushes).eval n :=
  (one_le_pairLength q n).trans (pairLength_le_capacity p q pushes n)

theorem transition_prefix_le_capacity (p q : Polynomial ℕ) (pushes n inputLength used extra : ℕ)
    (hi : inputLength ≤ (pairLengthPolynomial q).eval n)
    (ht : used < (horizonPolynomial p q).eval n) (he : extra ≤ pushes) :
    inputLength + used * pushes + extra ≤ (capacityPolynomial p q pushes).eval n := by
  have hu := Nat.mul_le_mul_right pushes (Nat.succ_le_of_lt ht)
  simp only [capacityPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  calc
    inputLength + used * pushes + extra ≤
        (pairLengthPolynomial q).eval n + (used + 1) * pushes := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    _ ≤ (pairLengthPolynomial q).eval n + (horizonPolynomial p q).eval n * pushes :=
      Nat.add_le_add_left hu _
    _ = _ := by rw [Nat.mul_comm ((horizonPolynomial p q).eval n) pushes]

theorem verifier_time_le_horizon (p q : Polynomial ℕ) (n witnessLength : ℕ)
    (hw : witnessLength ≤ q.eval n) :
    p.eval (2 * n + witnessLength + 1) ≤ (horizonPolynomial p q).eval n := by
  rw [horizonPolynomial, Polynomial.eval_comp]
  exact MachineComposition.natPolynomial_eval_mono p (paired_length_le q n witnessLength hw)

theorem horizon_monotone (p q : Polynomial ℕ) :
    Monotone (fun n => (horizonPolynomial p q).eval n) :=
  fun _ _ h => MachineComposition.natPolynomial_eval_mono _ h

theorem capacity_monotone (p q : Polynomial ℕ) (pushes : ℕ) :
    Monotone (fun n => (capacityPolynomial p q pushes).eval n) :=
  fun _ _ h => MachineComposition.natPolynomial_eval_mono _ h

theorem execution_stack_length_le_capacity (tm : Turing.FinTM2)
    (p q : Polynomial ℕ) (n : ℕ) (input : List (tm.Γ tm.k₀))
    (hi : input.length ≤ (pairLengthPolynomial q).eval n)
    (finish : tm.Cfg) (budget : ℕ)
    (ht : budget ≤ (horizonPolynomial p q).eval n)
    (run : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some finish) budget) (k : tm.K) :
    (finish.stk k).length ≤ (capacityPolynomial p q (Runtime.programPushBound tm)).eval n := by
  have hs := Runtime.executionSizeBound tm.step (fun cfg => (cfg.stk k).length)
    (Runtime.programPushBound tm) (Runtime.stepStackLength tm k) run
  have hinit := (Runtime.initialStackLength tm input k).trans hi
  have hg := Nat.mul_le_mul_right (Runtime.programPushBound tm) ht
  calc
    (finish.stk k).length ≤ ((Turing.initList tm input).stk k).length +
        budget * Runtime.programPushBound tm := hs
    _ ≤ (pairLengthPolynomial q).eval n +
        (horizonPolynomial p q).eval n * Runtime.programPushBound tm :=
      Nat.add_le_add hinit hg
    _ = _ := by simp [capacityPolynomial, Nat.mul_comm]

theorem stackCapacity_le_polynomial (tm : Turing.FinTM2)
    (p q : Polynomial ℕ) (n : ℕ) (input : List (tm.Γ tm.k₀))
    (hi : input.length ≤ (pairLengthPolynomial q).eval n) :
    BoundedExecution.stackCapacity tm input ((horizonPolynomial p q).eval n) ≤
      (capacityPolynomial p q (Runtime.programPushBound tm)).eval n := by
  simpa only [BoundedExecution.stackCapacity, capacityPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Nat.mul_comm] using
    Nat.add_le_add_right hi ((horizonPolynomial p q).eval n * Runtime.programPushBound tm)

theorem run_stack_length_le_capacity (tm : Turing.FinTM2)
    (p q : Polynomial ℕ) (n : ℕ) (input : List (tm.Γ tm.k₀))
    (hi : input.length ≤ (pairLengthPolynomial q).eval n)
    (time : ℕ) (ht : time ≤ (horizonPolynomial p q).eval n) (k : tm.K) :
    ((BoundedExecution.run tm input time).stk k).length ≤
      (capacityPolynomial p q (Runtime.programPushBound tm)).eval n :=
  (BoundedExecution.run_stack_le tm input _ time ht k).trans
    (stackCapacity_le_polynomial tm p q n input hi)

theorem run_statement_budget_le_capacity (tm : Turing.FinTM2)
    (p q : Polynomial ℕ) (n : ℕ) (input : List (tm.Γ tm.k₀))
    (hi : input.length ≤ (pairLengthPolynomial q).eval n)
    (time : ℕ) (ht : time < (horizonPolynomial p q).eval n)
    (label : tm.Λ) (k : tm.K) :
    ((BoundedExecution.run tm input time).stk k).length +
        Runtime.statementPushBound (tm.m label) ≤
      (capacityPolynomial p q (Runtime.programPushBound tm)).eval n :=
  (BoundedExecution.statement_budget tm input _ time ht label k).trans
    (stackCapacity_le_polynomial tm p q n input hi)

noncomputable def configurationWidthPolynomial (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits : ℕ) : Polynomial ℕ :=
  C controlBits + capacityPolynomial p q pushes * C alphabetBits

noncomputable def transitionGatesPolynomial (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits expressionCost : ℕ) : Polynomial ℕ :=
  C expressionCost * configurationWidthPolynomial p q pushes controlBits alphabetBits

noncomputable def tableauGatesPolynomial (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits expressionCost : ℕ) : Polynomial ℕ :=
  horizonPolynomial p q *
    transitionGatesPolynomial p q pushes controlBits alphabetBits expressionCost

@[simp] theorem configurationWidthPolynomial_eval (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits n : ℕ) :
    (configurationWidthPolynomial p q pushes controlBits alphabetBits).eval n =
      controlBits + (capacityPolynomial p q pushes).eval n * alphabetBits := by
  simp [configurationWidthPolynomial]

@[simp] theorem transitionGatesPolynomial_eval (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits expressionCost n : ℕ) :
    (transitionGatesPolynomial p q pushes controlBits alphabetBits expressionCost).eval n =
      expressionCost * (controlBits + (capacityPolynomial p q pushes).eval n * alphabetBits) := by
  simp [transitionGatesPolynomial]

@[simp] theorem tableauGatesPolynomial_eval (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits expressionCost n : ℕ) :
    (tableauGatesPolynomial p q pushes controlBits alphabetBits expressionCost).eval n =
      (horizonPolynomial p q).eval n * expressionCost *
        (controlBits + (capacityPolynomial p q pushes).eval n * alphabetBits) := by
  simp only [tableauGatesPolynomial, Polynomial.eval_mul, transitionGatesPolynomial_eval]
  exact (Nat.mul_assoc _ _ _).symm

noncomputable def formulaBitsPolynomial (varBound clauseBound : Polynomial ℕ) : Polynomial ℕ :=
  varBound + clauseBound + C 2 + clauseBound * (C 3 * (varBound + C 2))

@[simp] theorem formulaBitsPolynomial_eval (varBound clauseBound : Polynomial ℕ) (n : ℕ) :
    (formulaBitsPolynomial varBound clauseBound).eval n =
      varBound.eval n + clauseBound.eval n + 2 +
        clauseBound.eval n * (3 * (varBound.eval n + 2)) := by
  simp [formulaBitsPolynomial]

theorem formulaBits_length_le_polynomial (F : Target.Formula)
    (varBound clauseBound : Polynomial ℕ) (n : ℕ)
    (hv : F.variables ≤ varBound.eval n)
    (hc : F.clauses.length ≤ clauseBound.eval n) :
    (formulaBits F).length ≤ (formulaBitsPolynomial varBound clauseBound).eval n := by
  refine (formulaBits_length_le F).trans ?_
  rw [formulaBitsPolynomial_eval]
  exact Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add hv hc) 2)
    (Nat.mul_le_mul hc (Nat.mul_le_mul_left 3 (Nat.add_le_add_right hv 2)))

noncomputable def circuitVariablesPolynomial (inputs gates : Polynomial ℕ) : Polynomial ℕ :=
  inputs + gates

noncomputable def circuitClausesPolynomial (gates : Polynomial ℕ) : Polynomial ℕ :=
  C 3 * gates + 1

noncomputable def circuitBitsPolynomial (inputs gates : Polynomial ℕ) : Polynomial ℕ :=
  formulaBitsPolynomial (circuitVariablesPolynomial inputs gates)
    (circuitClausesPolynomial gates)

@[simp] theorem circuitVariablesPolynomial_eval (inputs gates : Polynomial ℕ) (n : ℕ) :
    (circuitVariablesPolynomial inputs gates).eval n = inputs.eval n + gates.eval n := by
  simp [circuitVariablesPolynomial]

@[simp] theorem circuitClausesPolynomial_eval (gates : Polynomial ℕ) (n : ℕ) :
    (circuitClausesPolynomial gates).eval n = 3 * gates.eval n + 1 := by
  simp [circuitClausesPolynomial]

@[simp] theorem circuitBitsPolynomial_eval (inputs gates : Polynomial ℕ) (n : ℕ) :
    (circuitBitsPolynomial inputs gates).eval n =
      (inputs.eval n + gates.eval n) + (3 * gates.eval n + 1) + 2 +
        (3 * gates.eval n + 1) * (3 * ((inputs.eval n + gates.eval n) + 2)) := by
  simp [circuitBitsPolynomial]

theorem circuit_formulaBits_length_le (F : Target.Formula) (inputCount gateCount : ℕ)
    (hv : F.variables ≤ inputCount + gateCount)
    (hc : F.clauses.length ≤ 3 * gateCount + 1) :
    (formulaBits F).length ≤
      (inputCount + gateCount) + (3 * gateCount + 1) + 2 +
        (3 * gateCount + 1) * (3 * ((inputCount + gateCount) + 2)) := by
  exact (formulaBits_length_le F).trans
    (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add hv hc) 2)
      (Nat.mul_le_mul hc (Nat.mul_le_mul_left 3 (Nat.add_le_add_right hv 2))))

theorem circuit_formulaBits_length_le_polynomial (F : Target.Formula)
    (inputCount gateCount : ℕ) (inputs gates : Polynomial ℕ) (n : ℕ)
    (hi : inputCount ≤ inputs.eval n) (hg : gateCount ≤ gates.eval n)
    (hv : F.variables ≤ inputCount + gateCount)
    (hc : F.clauses.length ≤ 3 * gateCount + 1) :
    (formulaBits F).length ≤ (circuitBitsPolynomial inputs gates).eval n := by
  apply formulaBits_length_le_polynomial
  · simpa using hv.trans (Nat.add_le_add hi hg)
  · simpa using hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hg) 1)

theorem toFormula_bits_length_le (circuit : Circuit) :
    (formulaBits circuit.toFormula).length ≤
      (circuit.inputs + circuit.gates.length) + (3 * circuit.gates.length + 1) + 2 +
        (3 * circuit.gates.length + 1) *
          (3 * ((circuit.inputs + circuit.gates.length) + 2)) :=
  circuit_formulaBits_length_le circuit.toFormula circuit.inputs circuit.gates.length
    (Circuit.toFormula_variables circuit).le (Circuit.toFormula_clause_count circuit).le

theorem toFormula_bits_length_le_polynomial (circuit : Circuit)
    (inputs gates : Polynomial ℕ) (n : ℕ)
    (hi : circuit.inputs ≤ inputs.eval n) (hg : circuit.gates.length ≤ gates.eval n) :
    (formulaBits circuit.toFormula).length ≤ (circuitBitsPolynomial inputs gates).eval n :=
  circuit_formulaBits_length_le_polynomial circuit.toFormula circuit.inputs circuit.gates.length
    inputs gates n hi hg
    (Circuit.toFormula_variables circuit).le (Circuit.toFormula_clause_count circuit).le

end BinPackingGames.Foundations.Complexity.CookLevin.Bounds

end OAI
