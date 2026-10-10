import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.Remaining

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineOverlayTable
open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingOverlayWords
open MachineCloudPadding

variable {A : Type}

theorem loopSteps_le {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    MachineCountedLoop.totalSteps (loopCost G H) n ≤ n * (pairBudget d e n + 1) + 1 := by
  apply MachineCountedLoop.totalSteps_le
  intro r hr
  rw [loopCost, dite_eq_left hr]
  exact pairSteps_le G H _ _ (outputPrefix_length_le G H _)

noncomputable def phasePolynomial (d e : Nat) : Polynomial Nat :=
  let x := Polynomial.X
  let C := Polynomial.C (R := Nat)
  let oldValue := C (d + e) * (x * C d) + x * C d + C 0
  let os := x + oldValue + C 8194
  let newValue := C (d + e) * (x * C e) + x * C e + C d
  let es := x + newValue + C MachineOverlayRows.trueBits.length + C 2
  let block := C d * os + C e * es
  let cap := x + x * C (d + e) + C 2 + x * block
  let oldCost := C 2 * x + C 8 * (x * C d) + oldValue + C 4 * os + C 8224
  let newCost := C 8 * (x * C e) + C 4 * es + newValue + C MachineOverlayRows.trueBits.length + C 28
  let pair := (C d * (oldCost + C 2 * (cap + C d * os) + C 1) + C 1) +
    (C e * (newCost + C 2 * (cap + C d * os + C e * es) + C 1) + C 1) +
    (C 3 * x + C 6)
  x * (pair + C 1) + C 1 + (C 2 * x + x * C d + C 8)

@[simp] theorem phasePolynomial_eval (d e n : Nat) :
    (phasePolynomial d e).eval n = n * (pairBudget d e n + 1) + 1 + cleanupSteps n (n * d) := by
  simp only [phasePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, pairBudget, outputCapacity, blockSize, oldSize, expanderSize,
    MachineLazyRows.rowSizeBound, MachineLazyRows.rowCostBound, MachineLazyRows.valueBound,
    MachineOverlayRows.rowSizeBound, MachineOverlayRows.rowCostBound,
    MachineOverlayRows.valueBound, cleanupSteps]

noncomputable def timePolynomial (d e : Nat) : Polynomial Nat :=
  Polynomial.C 12 * Polynomial.X + Polynomial.C 18 + phasePolynomial d e

theorem tableSteps_le {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    tableSteps G H ≤ (timePolynomial d e).eval ((PortTables.tableBits G).length + (rawExpander H).length) := by
  have hsplit := MachineTableSplit.exactSteps_le n (n * d)
    (MachineTableSplit.rowsBits (PortTables.graphTable G))
  have header : encodeWords [n, n * d] ++ MachineTableSplit.rowsBits (PortTables.graphTable G) =
      PortTables.tableBits G := (MachineTableSplit.tableBits_header_rows (PortTables.graphTable G)).symm
  rw [header, MachineTableSplit.timePolynomial_eval] at hsplit
  have hn := PortTables.vertices_le_tableBits_length G
  have hloop := loopSteps_le G H
  have hmono := natPolynomial_eval_mono (phasePolynomial d e)
    (show n ≤ (PortTables.tableBits G).length + (rawExpander H).length by omega)
  rw [phasePolynomial_eval] at hmono
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  unfold tableSteps preparationSteps
  omega

def tableInTime {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : A) :
    StateTransition.EvalsToInTime (TM2.step (program d e hd he))
      ⟨some (.inl .copyFirst), clean d e hd he a,
        initialTapes (PortTables.tableBits G) (rawExpander H)⟩
      (some ⟨none, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H) [] [] [] [] [] [] []
          (PortTables.tableBits (PreprocessingOverlayTables.overlay G H))⟩)
      ((timePolynomial d e).eval ((PortTables.tableBits G).length + (rawExpander H).length)) where
  steps := tableSteps G H
  evals_in_steps := tableTrace d e hd he G H a
  steps_le_m := tableSteps_le G H

def machine (d e : Nat) (hd : 0 < d) (he : 0 < e) : FinTM2 where
  K := Tape
  k₀ := graphArchive
  k₁ := output
  Γ _ := Bool
  Λ := Label d e
  main := .inl .copyFirst
  σ := State Unit d e
  initialState := clean d e hd he ()
  m := program d e hd he

theorem machine_alphabet_finite (d e : Nat) (hd : 0 < d) (he : 0 < e) :
    ∀ k, Finite ((machine d e hd he).Γ k) := fun _ => inferInstanceAs (Finite Bool)

end IndependentSetsGames.Foundations.Complexity.MachineOverlayTable

end OAI
