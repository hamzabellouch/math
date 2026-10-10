import OAI.Computability.UniqueGames.Machines.MachineExpanderTableLoop
import OAI.Computability.UniqueGames.Machines.MachineExpanderTableReverse

namespace OAI

/-!
# Complete finite machine execution for the next expander table

The initialized old table and unary vertex count are consumed by one actual
finite program. The machine writes precisely the complete square/zigzag
rotation table, preserving its old table and all promised framing. The bound
is quadratic in the unary old-table length for each fixed small graph.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

def completeBudget {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d) : Nat :=
  1 + vertexLoopBudget G v + ((encodeWords (rotationWords (step G H))).length + 2)

def timeCoefficient (d : Nat) : Nat :=
  rowFactor d * (rowFactor d + 1) + 82 * rowFactor d + 5

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C (timeCoefficient d) * (Polynomial.X + 1) ^ 2

theorem vertices_le_word_length {v d : Nat} (positive : 0 < d)
    (G : Table v (degree d)) : v ≤ (oldTableWord G).length := by
  have hq : 1 ≤ degree d := Nat.mul_pos positive positive
  have hv : v ≤ v * degree d := by simpa using Nat.mul_le_mul_left v hq
  have hr : v * degree d ≤ (oldTableWord G).length := by
    simp only [oldTableWord, encodeWords_length, rotationWords_length]
    omega
  exact hv.trans hr

/-- All actual loop, row, and final reversal costs are bounded quadratically. -/
theorem completeBudget_le {v d : Nat} (positive : 0 < d)
    (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    completeBudget G H ≤ (timePolynomial d).eval (oldTableWord G).length := by
  let L := (oldTableWord G).length
  let M := rowFactor d
  have vBound : v ≤ L + 1 := (vertices_le_word_length positive G).trans (Nat.le_succ L)
  have emitBound : 80 * (L + 1) + 2 ≤ 82 * (L + 1) := by omega
  have bodyBound : vertexBodyBudget G + 1 ≤ (82 * M + 1) * (L + 1) := by
    have mulBound := Nat.mul_le_mul_left M emitBound
    change M * (80 * (L + 1) + 2) + 1 ≤ _
    nlinarith
  have iterations := Nat.mul_le_mul vBound bodyBound
  have loopBound : v * (vertexBodyBudget G + 1) ≤ (82 * M + 1) * (L + 1)^2 := by
    calc
      _ ≤ (L + 1) * ((82 * M + 1) * (L + 1)) := iterations
      _ = _ := by ring
  have rowBound : v * M ≤ M * (L + 1) := by
    simpa only [Nat.mul_comm v M] using Nat.mul_le_mul_left M vBound
  have rowSuccBound : v * M + 1 ≤ (M + 1) * (L + 1) := by nlinarith
  have productBound := Nat.mul_le_mul rowBound rowSuccBound
  have lengthBound : (encodeWords (rotationWords (step G H))).length ≤
      M * (M + 1) * (L + 1)^2 := by
    calc
      _ ≤ (v * M) * (v * M + 1) := by
        simpa only [generatedWords_eq_rotationWords] using encode_generatedWords_length_le G H
      _ ≤ (M * (L + 1)) * ((M + 1) * (L + 1)) := productBound
      _ = _ := by ring
  have oneBound : 1 ≤ (L + 1)^2 := by nlinarith
  have combined := Nat.add_le_add loopBound lengthBound
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  change completeBudget G H ≤ (M * (M + 1) + 82 * M + 5) * (L + 1)^2
  unfold completeBudget vertexLoopBudget
  nlinarith

structure TableRun {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .initialize), state, initialTapes v (oldTableWord G) suffix⟩
    (some ⟨none, finalState,
      finalTapes v (oldTableWord G) (encodeWords (rotationWords (step G H))) suffix⟩)
    ((timePolynomial d).eval (oldTableWord G).length)

private def initializeInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (state : State ρ d) (suffix : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .initialize), state, initialTapes v (oldTableWord G) suffix⟩
      (some ⟨some (.inr .vertexGuard), initialState positive H (caller state),
        vertexLoopTapes G H 0 v suffix⟩) 1 where
  steps := 1
  evals_in_steps := by
    change TM2.step (program (ρ := ρ) positive H)
      ⟨some (.inr .initialize), state, initialTapes v (oldTableWord G) suffix⟩ =
      some ⟨some (.inr .vertexGuard), initialState positive H (caller state),
        vertexLoopTapes G H 0 v suffix⟩
    simpa only [vertexLoopTapes, accumulatedVertices_zero] using
      initialize_boundaryStep positive H v (oldTableWord G) suffix state
  steps_le_m := Nat.le_refl _

/-- Construct the entire table execution from its actual initialized inputs.
No row trace, loop trace, or abstract computational witness is a hypothesis. -/
def tableInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (state : State ρ d) (suffix : List Bool) : TableRun positive G H state suffix := by
  let loop := vertexLoopInTime positive G H 0 v
    (initialState positive H (caller state)) suffix (by omega) rfl
  let initialRun := initializeInTime positive G H state suffix
  have finish : StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .reverseOutput), loop.finalState, vertexLoopTapes G H v 0 suffix⟩
      (some ⟨none, clearRegister loop.finalState,
        finalTapes v (oldTableWord G) (encodeWords (rotationWords (step G H))) suffix⟩)
      ((encodeWords (rotationWords (step G H))).length + 2) := by
    simpa only [vertexLoopTapes, finalTapes, accumulatedVertices_full, List.reverse_reverse,
      List.append_nil, List.length_reverse] using
      reverseOutputHaltInTime positive H v 0 (oldTableWord G)
        (accumulatedVertices G H v) suffix [] loop.finalState
  let first := StateTransition.EvalsToInTime.trans (TM2.step (program positive H))
    _ _ _ _ _ initialRun loop.execution
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H))
    _ _ _ _ _ first finish
  refine ⟨clearRegister loop.finalState, ?_, ?_, ?_⟩
  · exact (caller_clearRegister loop.finalState).trans loop.caller_preserved
  · simpa only [clearRegister] using loop.position_zero
  · refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
    have bound := all.steps_le_m
    have polynomialBound := completeBudget_le positive G H
    unfold completeBudget at polynomialBound
    omega

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

end OAI
