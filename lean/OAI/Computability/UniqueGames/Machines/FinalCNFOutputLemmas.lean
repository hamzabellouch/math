import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Machines.FinalCNFLoopLemmas
import OAI.Computability.UniqueGames.Machines.FinalCNFMachineLemmas
import OAI.Computability.UniqueGames.Machines.FinalCNFRowPlanLemmas
import OAI.Computability.UniqueGames.Machines.FinalCNFStream
import OAI.Computability.UniqueGames.PCP.FinalTableFormula

namespace OAI


/-!
The final machine's complete output stream is the exact serialization of its
actual formula. This identity includes the two size fields, every clause and
literal field, and all unary delimiters. No desired output equality is assumed.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open PCP

section Alphabet

open PCP.AlphabetTable


def formulaHeader (table : GraphTables.Table) : List Bool :=
  encodeWords [6 * table.vertices + 36864 * table.darts, 40960 * table.darts]

theorem formulaHeader_eq (table : GraphTables.Table) :
    formulaHeader table = encodeWords [(FinalTableFormula.output table).variables,
      (FinalTableFormula.output table).clauses.length] := by
  simp only [formulaHeader, FinalTableFormula.variable_count, FinalTableFormula.clause_count,
    Nat.mul_comm]

theorem headerPlan_eq_formulaHeader (table : GraphTables.Table) (tail head row : Nat)
    (ambient : Ambient) :
    headerPlan.flatMap (Emitter.commandBits
      (values table.vertices table.darts tail head row) ambient) = formulaHeader table :=
  headerPlan_bits table.vertices table.darts tail head row ambient

theorem outputStream_eq_clauseBits (table : GraphTables.Table) :
    outputStream rowPlan table (List.finRange table.darts) =
      encodeWords ((FinalTableFormula.output table).clauses.flatMap Complexity.clauseWords) := by
  calc
    _ = (List.finRange table.darts).flatMap (fun e =>
          encodeWords ((VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
            (by decide) e).flatMap Complexity.clauseWords)) := by
      apply List.flatMap_congr
      intro e he
      exact rowPlan_bits table e
    _ = encodeWords ((List.finRange table.darts).flatMap (fun e =>
          (VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
            (by decide) e).flatMap Complexity.clauseWords)) :=
      (encodeWords_flatMap _ _).symm
    _ = _ := by
      congr 1
      rw [← List.flatMap_assoc]
      rfl

theorem header_append_outputStream (table : GraphTables.Table) :
    formulaHeader table ++ outputStream rowPlan table (List.finRange table.darts) =
      formulaBits (FinalTableFormula.output table) := by
  rw [formulaHeader_eq, outputStream_eq_clauseBits]
  exact (encodeWords_append _ _).symm

theorem emitted_output_eq (table : GraphTables.Table) (tail head row : Nat)
    (ambient : Ambient) :
    headerPlan.flatMap (Emitter.commandBits
      (values table.vertices table.darts tail head row) ambient) ++
      outputStream rowPlan table (List.finRange table.darts) =
        formulaBits (FinalTableFormula.output table) := by
  rw [headerPlan_eq_formulaHeader]
  exact header_append_outputStream table

/-- Reversing the finished stack accumulator restores the required output order. -/
theorem reversed_accumulator_output (table : GraphTables.Table) :
    (formulaHeader table ++ outputStream rowPlan table (List.finRange table.darts)).reverse.reverse =
      formulaBits (FinalTableFormula.output table) := by
  rw [List.reverse_reverse, header_append_outputStream]

theorem accumulator_length_bound (table : GraphTables.Table) :
    (formulaHeader table ++ outputStream rowPlan table (List.finRange table.darts)).reverse.length ≤
      FinalTableFormula.sizePolynomial.eval (GraphTables.tableBits table).length := by
  rw [List.length_reverse, header_append_outputStream]
  exact FinalTableFormula.formulaBits_length_le_polynomial table

end Alphabet

noncomputable def rowTimePolynomial : Polynomial Nat :=
  Polynomial.C 860160 * (Polynomial.C 3 * (Polynomial.X + Polynomial.C 1) + Polynomial.C 3) +
    Polynomial.C 12 * Polynomial.X + Polynomial.C 15

theorem rowTimePolynomial_eval (N : Nat) :
    rowTimePolynomial.eval N = rowTime rowPlan N := by
  simp only [rowTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, rowTime, rowPlan_length]

theorem rowTime_expanded (N : Nat) : rowTime rowPlan N = 2580492 * N + 5160975 := by
  rw [rowTime, rowPlan_length]
  omega

/-- Header, at most `N` rows with guards, and the final output reversal. -/
noncomputable def phaseTimePolynomial : Polynomial Nat :=
  headerTimePolynomial +
    (Polynomial.X * (rowTimePolynomial + Polynomial.C 1) + Polynomial.C 1) +
    (FinalTableFormula.sizePolynomial + Polynomial.C 1)

theorem phaseTimePolynomial_eval (N : Nat) :
    phaseTimePolynomial.eval N =
      headerTimePolynomial.eval N + (N * (rowTime rowPlan N + 1) + 1) +
        (FinalTableFormula.sizePolynomial.eval N + 1) := by
  simp only [phaseTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, rowTimePolynomial_eval]

theorem phaseTimePolynomial_eval_expanded (N : Nat) :
    phaseTimePolynomial.eval N = 4532428812 * N ^ 2 + 5484585 * N + 56 := by
  rw [phaseTimePolynomial_eval, headerTimePolynomial_eval, rowTime_expanded,
    FinalTableFormula.sizePolynomial_eval]
  ring

theorem phaseTime_le {N rows outputLength : Nat} (rowBound : rows ≤ N)
    (outputBound : outputLength ≤ FinalTableFormula.sizePolynomial.eval N) :
    headerTimePolynomial.eval N + (rows * (rowTime rowPlan N + 1) + 1) +
      (outputLength + 1) ≤ phaseTimePolynomial.eval N := by
  have hrows := Nat.mul_le_mul_right (rowTime rowPlan N + 1) rowBound
  rw [phaseTimePolynomial_eval]
  omega

/-- The bound specialized to the actual table and actual formula serialization. -/
theorem table_phaseTime_le (table : GraphTables.Table) :
    headerTimePolynomial.eval (GraphTables.tableBits table).length +
      (table.darts * (rowTime rowPlan (GraphTables.tableBits table).length + 1) + 1) +
      ((formulaBits (FinalTableFormula.output table)).length + 1) ≤
        phaseTimePolynomial.eval (GraphTables.tableBits table).length :=
  phaseTime_le (GraphTables.darts_le_tableBits_length table)
    (FinalTableFormula.formulaBits_length_le_polynomial table)

/-- Twelve private stacks are drained, then the finite state is reset.
`C` is the fixed maximum number of pushes in a raw-program transition. -/
noncomputable def finalTimePolynomial (C : Nat) : Polynomial Nat :=
  phaseTimePolynomial + Polynomial.C 12 *
    (Polynomial.X + phaseTimePolynomial * Polynomial.C C + Polynomial.C 1) + Polynomial.C 1

theorem finalTimePolynomial_eval (C N : Nat) :
    (finalTimePolynomial C).eval N = phaseTimePolynomial.eval N +
      12 * (N + phaseTimePolynomial.eval N * C + 1) + 1 := by
  simp only [finalTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

/-- Pure budget composition; the drain implementation supplies its own trace. -/
theorem finalTime_le (C N workLength : Nat)
    (workBound : workLength ≤ N + phaseTimePolynomial.eval N * C) :
    phaseTimePolynomial.eval N + 12 * (workLength + 1) + 1 ≤
      (finalTimePolynomial C).eval N := by
  have h := Nat.mul_le_mul_left 12 (Nat.add_le_add_right workBound 1)
  rw [finalTimePolynomial_eval]
  omega

/-!
The complete polynomial-time machine certificate for converting a validated
64-label graph table into its actual 3CNF formula. The proof composes the real
input parser, all row executions, output reversal, and private-tape cleanup.
-/

open Turing


theorem emittedBytes_eq_formulaBits (table : GraphTables.Table) :
    emittedBytes rowPlan table = formulaBits (FinalTableFormula.output table) :=
  header_append_outputStream table

theorem rawBudget_le_phaseTime (table : GraphTables.Table) :
    rawBudget rowPlan table ≤ phaseTimePolynomial.eval (GraphTables.tableBits table).length := by
  unfold rawBudget
  rw [emittedBytes_eq_formulaBits]
  simpa only [Nat.add_assoc] using table_phaseTime_le table

/-- A concrete finite machine computes the complete CNF serialization from
the exact unary graph-table serialization, with a proved polynomial bound. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime GraphTables.tableBits formulaBits FinalTableFormula.output where
  tm := FinalCNFCleanup.completedMachine headerPlan rowPlan
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := finalTimePolynomial (Runtime.programPushBound (machine headerPlan rowPlan))
  outputsFun table := by
    change TM2OutputsInTime (FinalCNFCleanup.completedMachine headerPlan rowPlan)
      ((GraphTables.tableBits table).map id)
      (some ((formulaBits (FinalTableFormula.output table)).map id))
      ((finalTimePolynomial (Runtime.programPushBound (machine headerPlan rowPlan))).eval
        (GraphTables.tableBits table).length)
    have input_eq :
        @List.map ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
            (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₀)
          ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
            (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₀)
          id (GraphTables.tableBits table) = GraphTables.tableBits table := List.map_id _
    have output_eq :
        @List.map ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
            (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₁)
          ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
            (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₁)
          id (formulaBits (FinalTableFormula.output table)) =
          formulaBits (FinalTableFormula.output table) := List.map_id _
    rw [input_eq, output_eq, finalTimePolynomial_eval]
    let raw := rawRun rowPlan table
    let bounded : StateTransition.EvalsToInTime (machine headerPlan rowPlan).step
        (initList (machine headerPlan rowPlan) (GraphTables.tableBits table))
        (some ⟨none, ((raw.finalAmbient, ()), none), raw.finalTapes⟩)
        (phaseTimePolynomial.eval (GraphTables.tableBits table).length) := {
      toEvalsTo := raw.execution.toEvalsTo
      steps_le_m := raw.execution.steps_le_m.trans (rawBudget_le_phaseTime table) }
    have correct : raw.finalTapes .output = formulaBits (FinalTableFormula.output table) :=
      raw.output.trans (emittedBytes_eq_formulaBits table)
    have run := FinalCNFCleanup.outputsInTime headerPlan rowPlan
      (GraphTables.tableBits table) (formulaBits (FinalTableFormula.output table))
      ((raw.finalAmbient, ()), none) raw.finalTapes
      (phaseTimePolynomial.eval (GraphTables.tableBits table).length) bounded correct
    exact run

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
