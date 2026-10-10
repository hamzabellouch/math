import OAI.Computability.UniqueGames.Machines.MachineCanonicalOutputLemmas
import OAI.Computability.UniqueGames.Machines.MachineRegularOriginalBodyBounds
import OAI.Computability.UniqueGames.Machines.MachineRegularOwnerBodyBounds
import OAI.Computability.UniqueGames.Machines.MachineRegularTableTrace
import OAI.Computability.UniqueGames.PCP.PreprocessingTablesLemmas

namespace OAI


/-! A polynomial cap for the actual two regularization loops, their header,
and all seven final drain loops. Per-call sizes include the complete stored
output prefix. -/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top

open Turing MachineComposition PCP PreprocessingRegularTables
open PreprocessingRegularBounds PreprocessingMachineBounds


noncomputable def oldLoopPolynomial : Polynomial Nat :=
  Polynomial.X *
    (MachineRegularOriginalBodyBounds.timePolynomial.comp
      (Polynomial.X + regularPolynomial) + 2)

noncomputable def ownerLoopPolynomial : Polynomial Nat :=
  Polynomial.X *
    (MachineRegularOwnerBodyBounds.timePolynomial.comp
      (Polynomial.X + regularPolynomial) + 2)

noncomputable def timePolynomial : Polynomial Nat :=
  Header.timePolynomial internalDegree + oldLoopPolynomial + ownerLoopPolynomial +
    4 * Polynomial.X + 12 +
    Polynomial.C (7 * (ExpanderFamily.growth * (internalDegree + 4) + 4)) *
      (Polynomial.X + 1)

theorem oldElapsed_prefix_le (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    oldElapsed H t (Header.headerBits internalDegree t) k ≤
      k * (MachineRegularOriginalBodyBounds.timePolynomial.eval
        (inputLength t + regularPolynomial.eval (inputLength t)) + 2) := by
  induction k with
  | zero => simp [oldElapsed]
  | succ k ih =>
    simp only [oldElapsed]
    split_ifs with hk
    · have raw := MachineRegularOriginalBodyBounds.totalSteps_le H t ⟨k, hk⟩
        (Header.headerBits internalDegree t ++ oldPrefix H t k)
      have hprefix :
          (Header.headerBits internalDegree t ++ oldPrefix H t k).length ≤
            regularPolynomial.eval (inputLength t) := by
        exact regular_originalPrefix_le t H k
      have hcall := raw.trans (natPolynomial_eval_mono
        MachineRegularOriginalBodyBounds.timePolynomial (Nat.add_le_add_left hprefix _))
      rw [Nat.succ_mul]
      omega
    · rw [Nat.succ_mul]
      omega

theorem oldElapsed_le (H : BaseTable) (t : GraphTables.Table) :
    oldElapsed H t (Header.headerBits internalDegree t) t.darts ≤
      oldLoopPolynomial.eval (inputLength t) := by
  have bound := (oldElapsed_prefix_le H t t.darts).trans
    (Nat.mul_le_mul_right _ (GraphTables.darts_le_tableBits_length t))
  simpa only [oldLoopPolynomial, inputLength, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_ofNat] using bound

theorem ownerElapsed_prefix_le (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    ownerElapsed H t
      (Header.headerBits internalDegree t ++ oldPrefix H t t.darts) k ≤
      k * (MachineRegularOwnerBodyBounds.timePolynomial.eval
        (inputLength t + regularPolynomial.eval (inputLength t)) + 2) := by
  induction k with
  | zero => simp [ownerElapsed]
  | succ k ih =>
    simp only [ownerElapsed]
    split_ifs with hk
    · have raw := MachineRegularOwnerBodyBounds.totalSteps_le H t ⟨k, hk⟩
        ((Header.headerBits internalDegree t ++ oldPrefix H t t.darts) ++ ownerPrefix H t k)
      have hprefix :
          ((Header.headerBits internalDegree t ++ oldPrefix H t t.darts) ++
            ownerPrefix H t k).length ≤ regularPolynomial.eval (inputLength t) := by
        rw [owner_output_eq_ownerPrefix]
        exact regular_ownerPrefix_le t H k
      have hcall := raw.trans (natPolynomial_eval_mono
        MachineRegularOwnerBodyBounds.timePolynomial (Nat.add_le_add_left hprefix _))
      rw [Nat.succ_mul]
      omega
    · rw [Nat.succ_mul]
      omega

theorem ownerElapsed_le (H : BaseTable) (t : GraphTables.Table) :
    ownerElapsed H t
      (Header.headerBits internalDegree t ++ oldPrefix H t t.darts) t.vertices ≤
      ownerLoopPolynomial.eval (inputLength t) := by
  have bound := (ownerElapsed_prefix_le H t t.vertices).trans
    (Nat.mul_le_mul_right _ (GraphTables.vertices_le_tableBits_length t))
  simpa only [ownerLoopPolynomial, inputLength, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_ofNat] using bound

theorem totalTime_le (H : BaseTable) (t : GraphTables.Table) :
    totalTime H t ≤ timePolynomial.eval (inputLength t) := by
  have header := Header.totalTime_le internalDegree t []
  simp only [List.length_nil, Nat.add_zero] at header
  change Header.totalTime internalDegree t [] ≤
    (Header.timePolynomial internalDegree).eval (inputLength t) at header
  have old := oldElapsed_le H t
  have owners := ownerElapsed_le H t
  have cleanup := cleanupTime_final_le t (finalOutput H t)
  have hm : t.darts ≤ inputLength t := GraphTables.darts_le_tableBits_length t
  have hn : t.vertices ≤ inputLength t := GraphTables.vertices_le_tableBits_length t
  simp only [totalTime, headerOutput, oldOutput, timePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

noncomputable def machineInTime (H : BaseTable) (t : GraphTables.Table) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      (initList (machine H) (GraphTables.tableBits t))
      (some ⟨none, readyState H,
        Function.update (initList (machine H) (GraphTables.tableBits t)).stk
          (coreTape 8) (PortTables.tableBits (regularize H t))⟩)
      (timePolynomial.eval (inputLength t)) where
  steps := totalTime H t
  evals_in_steps := trace H t
  steps_le_m := totalTime_le H t

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top



namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTableRuntime

open Turing
open PCP
open MachineRegularTable.Top (Tape Label State coreTape readyState)


def rawProgram (H : PreprocessingRegularTables.BaseTable) :
    MachineCanonicalOutput.Program Tape Label State where
  input := coreTape 0
  output := coreTape 8
  main := .header .init
  initial := readyState H
  code := MachineRegularTable.Top.program H

theorem sourceMachine_eq (H : PreprocessingRegularTables.BaseTable) :
    MachineCanonicalOutput.sourceMachine (rawProgram H) =
      MachineRegularTable.Top.machine H := rfl

noncomputable def cleanupTapes : List Tape :=
  (Finset.univ : Finset Tape).toList.filter (fun k => decide (k ≠ coreTape 8))

theorem cleanup_complete (H : PreprocessingRegularTables.BaseTable) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram H).output := by
  simp [cleanupTapes, rawProgram]

noncomputable def terminalRun (H : PreprocessingRegularTables.BaseTable)
    (t : GraphTables.Table) :
    MachineCanonicalOutput.TerminalRun (rawProgram H) (GraphTables.tableBits t)
      (PortTables.inputBits (PreprocessingStageMaps.regular H t))
      (MachineRegularTable.Top.timePolynomial.eval (GraphTables.tableBits t).length) where
  state := readyState H
  tapes := Function.update
    (initList (MachineRegularTable.Top.machine H) (GraphTables.tableBits t)).stk
    (coreTape 8) (PortTables.inputBits (PreprocessingStageMaps.regular H t))
  execution := by
    simpa only [sourceMachine_eq, FinTM2.Cfg, FinTM2.step, MachineRegularTable.Top.machine,
      PreprocessingMachineBounds.inputLength, PreprocessingStageMaps.regular,
      PortTables.inputBits] using!
      MachineRegularTable.Top.machineInTime H t
  output_eq := by
    dsimp only [rawProgram]
    erw [Function.update_self]

/-- The literal canonical output configuration computes the shared regular
preprocessing map, with the actual complete raw execution as its witness. -/
noncomputable def computableInPolyTime (H : PreprocessingRegularTables.BaseTable) :
    TM2ComputableInPolyTime GraphTables.tableBits
      (PortTables.inputBits (ports := PreprocessingRegularTables.internalDegree + 1))
      (PreprocessingStageMaps.regular H) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram H) cleanupTapes
    (cleanup_complete H) GraphTables.tableBits PortTables.inputBits
    (PreprocessingStageMaps.regular H) MachineRegularTable.Top.timePolynomial (terminalRun H)

/-- Finiteness refers to the exact machine in the preceding certificate. -/
theorem finite_alphabet (H : PreprocessingRegularTables.BaseTable) :
    ∀ k, Finite ((computableInPolyTime H).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram H) cleanupTapes
    (cleanup_complete H) GraphTables.tableBits PortTables.inputBits
    (PreprocessingStageMaps.regular H) MachineRegularTable.Top.timePolynomial (terminalRun H)

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTableRuntime

end OAI
