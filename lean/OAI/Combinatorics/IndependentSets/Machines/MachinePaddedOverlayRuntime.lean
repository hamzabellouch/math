import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachinePaddedOverlay

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachinePaddedOverlayRuntime

open Turing
open PCP
open MachinePaddedOverlay (BaseTable Tape Label State)

def rawProgram (H : BaseTable) (d : Nat) (hd : 0 < d) :
    MachineCanonicalOutput.Program Tape (Label d) (State d) where
  input := .inl .original
  output := .inr (.inr MachineOverlayTable.output)
  main := MachinePaddedOverlay.main
  initial := MachinePaddedOverlay.clean H d hd
  code := MachinePaddedOverlay.program H d hd

theorem sourceMachine_eq (H : BaseTable) (d : Nat) (hd : 0 < d) :
    MachineCanonicalOutput.sourceMachine (rawProgram H d hd) =
      MachinePaddedOverlay.machine H d hd := rfl

noncomputable def cleanupTapes : List Tape :=
  (Finset.univ.erase (.inr (.inr MachineOverlayTable.output) : Tape)).toList

theorem cleanup_complete (H : BaseTable) (d : Nat) (hd : 0 < d) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram H d hd).output := by
  simp [cleanupTapes, rawProgram]

theorem initial_configuration (H : BaseTable) (d : Nat) (hd : 0 < d)
    (a : PortTables.Input d) :
    initList (MachineCanonicalOutput.sourceMachine (rawProgram H d hd))
        (PortTables.inputBits a) =
      ⟨some MachinePaddedOverlay.main, MachinePaddedOverlay.clean H d hd,
        MachinePaddedOverlay.initialTapes a.2⟩ := by
  change initList (MachinePaddedOverlay.machine H d hd) (PortTables.tableBits a.2) = _
  exact MachinePaddedOverlay.initial_configuration H hd a.2

noncomputable def terminalRun (H : BaseTable) (d : Nat) (hd : 0 < d)
    (a : PortTables.Input d) :
    MachineCanonicalOutput.TerminalRun (rawProgram H d hd) (PortTables.inputBits a)
      (PortTables.inputBits (PreprocessingStageMaps.paddedOverlay H d a))
      ((MachinePaddedOverlay.timePolynomial d).eval (PortTables.inputBits a).length) where
  state := MachinePaddedOverlay.clean H d hd
  tapes := MachinePaddedOverlay.finalTapes H a.2
  execution := by
    rw [initial_configuration]
    exact MachinePaddedOverlay.execution H hd a.2
  output_eq := MachinePaddedOverlay.final_output H hd a.2

noncomputable def computableInPolyTime (H : BaseTable) (d : Nat) (hd : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := d + MachinePaddedOverlay.overlayDegree))
      (PreprocessingStageMaps.paddedOverlay H d) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram H d hd) cleanupTapes
    (cleanup_complete H d hd) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.paddedOverlay H d) (MachinePaddedOverlay.timePolynomial d)
    (terminalRun H d hd)

theorem finite_alphabet (H : BaseTable) (d : Nat) (hd : 0 < d) :
    ∀ k, Finite ((computableInPolyTime H d hd).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram H d hd) cleanupTapes
    (cleanup_complete H d hd) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.paddedOverlay H d) (MachinePaddedOverlay.timePolynomial d)
    (terminalRun H d hd)

end IndependentSetsGames.Foundations.Complexity.MachinePaddedOverlayRuntime
namespace IndependentSetsGames.Foundations.Complexity.MachineLazyCodec
open PCP.GraphTables PCP.PreprocessingLazyWords

theorem rowsBits_ofFn (v e count : Nat) :
    MachineDummyRows.rowsBits v e count =
      (List.ofFn fun p : Fin count => MachineDummyRows.rowBits v (e + p.val)).flatten := by
  induction count generalizing e with
  | zero => rfl
  | succ count ih =>
    rw [MachineDummyRows.rowsBits, List.ofFn_succ, List.flatten_cons]
    simp only [Fin.val_zero, Nat.add_zero]
    apply congrArg (MachineDummyRows.rowBits v e ++ ·)
    rw [ih]
    apply congrArg List.flatten
    congr 1
    funext p
    simp only [Fin.val_succ]
    congr 1
    omega

theorem encodeWords_flatMap {α : Type*} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun x => encodeWords (words x)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem rowBits_stay {n d : Nat} (v : Fin n) (p : Fin d) :
    MachineDummyRows.rowBits v.val (2 * d * v.val + p.val) =
      encodeWords (rowWords (stayRow d v p)) := by
  have h := MachineDummyRows.rowBits_eq_graph_row v (stayRow d v p).reverseIndex
  rw [stayRow_reverse_val] at h
  exact h

theorem rowsBits_stay {n d : Nat} (v : Fin n) :
    MachineDummyRows.rowsBits v.val (2 * d * v.val) d =
      encodeWords ((List.ofFn (stayRow d v)).flatMap rowWords) := by
  rw [rowsBits_ofFn, encodeWords_flatMap]
  simp only [List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  congr 1
  funext p
  exact rowBits_stay v p

end IndependentSetsGames.Foundations.Complexity.MachineLazyCodec

end OAI
