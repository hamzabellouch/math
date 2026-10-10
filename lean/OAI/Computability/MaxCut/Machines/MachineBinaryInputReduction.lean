import Mathlib
import OAI.Computability.MaxCut.Machines.MachineClone100
import OAI.Computability.MaxCut.Machines.MachineBinaryRenameWords
import OAI.Computability.MaxCut.Games.NP

namespace OAI

/-!
The complete ordinary-binary input bridge. Arbitrary raw input bits are first
validated and retained, or replaced by a fixed contradictory encoded formula.
The checked occurrence-index renamer then emits the inherited dense 3CNF
codec. Both stages and their physical handoff have actual polynomial-time
finite-alphabet machine certificates.

This is a bridge for the explicit ordinary binary 3SAT language. It is not the
PCP construction, a proof of that construction's runtime, or an NP-hardness
assertion about the eventual 2-to-1 target.
-/

namespace MaxCutGames.BinaryInputReduction

open Turing MaxCutGames.Foundations.Complexity

/-- The actual sequential machine handles every bitstring, including malformed
and noncanonical encodings, and outputs the fixed dense formula serialization. -/
noncomputable def computation :
    TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits BinaryLanguage.totalRename := by
  change TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits
    (fun input => BinaryOccurrenceRename.renamed (BinaryLanguage.totalParsed input))
  exact MachineSequential.composeBits BinaryTotalInputMachine.computableInPolyTime
    BinaryRenameMachine.computableInPolyTime

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineFiniteAlphabet.composeBits BinaryTotalInputMachine.computableInPolyTime
    BinaryRenameMachine.computableInPolyTime
    BinaryTotalInputMachine.computation_finiteAlphabet
    BinaryRenameMachine.computation_finiteAlphabet

/-- Satisfiability equivalence plus an actual raw-bit machine; no external
verifier, parsing-time assertion, or recoding hypothesis is an input. -/
noncomputable def reduction : CookLevin.PolynomialThreeSATReduction BinaryLanguage.language where
  reduce := BinaryLanguage.totalRename
  computation := computation
  correct input := (BinaryLanguage.totalRename_satisfiable_iff input).symm

theorem reduction_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet reduction.computation.tm :=
  computation_finiteAlphabet

end MaxCutGames.BinaryInputReduction

end OAI
