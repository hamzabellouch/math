import OAI.Computability.PerfectCompleteness.Machines.NormalizedTargetMachine
import OAI.Computability.PerfectCompleteness.Reduction.PreliminaryOutputLemmas

namespace OAI

section

namespace PerfectCompleteness.FixedTarget

open Turing UniqueGamesTheorem.Foundations.Complexity
open FixedParameters FixedRows FixedPreliminaryGame

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

def alphabet : Nat :=
  FinitePreliminaryCompletion.alphabet (branch p) p.plan.depth
    (sourceLength p.plan hδ) δ

theorem alphabet_ge_two : 2 ≤ alphabet p :=
  CanonicalLocalCompletion.alphabet_ge_two
    (TreeCanonical.locationCount (branch p) p.plan.depth (sourceLength p.plan hδ)) δ

theorem alphabet_pos : 0 < alphabet p :=
  lt_of_lt_of_le (by decide : 0 < 2) (alphabet_ge_two p)

def construct (input : List Bool) : Instance (alphabet p) :=
  NormalizedTarget.construct (branch := branch p) (n := p.plan.depth)
    (t := sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
    (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1)) δ
    (NormalizedSourceInput.raw input)

def computation :
    TM2ComputableInPolyTime (id : List Bool → List Bool) Encoding.gameBits
      (construct p) := by
  change TM2ComputableInPolyTime (id : List Bool → List Bool) Encoding.gameBits
    (fun input => NormalizedTarget.construct (branch := branch p) (n := p.plan.depth)
      (t := sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
      (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1)) δ
      (NormalizedSourceInput.raw input))
  exact MachineSequential.composeBits
    NormalizedSourceInput.rawComputation
    (NormalizedTargetMachine.targetComputation (branch := branch p) (n := p.plan.depth)
      (t := sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
      (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1)) δ)

theorem finiteAlphabet :
    MachineFiniteAlphabet.FiniteAlphabet (computation p).tm :=
  MachineFiniteAlphabet.composeBits
    NormalizedSourceInput.rawComputation
    (NormalizedTargetMachine.targetComputation (branch := branch p) (n := p.plan.depth)
      (t := sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
      (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1)) δ)
    NormalizedSourceInput.raw_finiteAlphabet
    (NormalizedTargetMachine.finiteAlphabet (branch := branch p) (n := p.plan.depth)
      (t := sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
      (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1)) δ)

theorem perfectlyComplete (input : List Bool) (accepted : BinaryLanguage.language input) :
    PerfectlyComplete (construct p input) :=
  NormalizedTarget.perfectlyComplete (branch := branch p) (n := p.plan.depth)
    (t := sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
    (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1)) δ
    (NormalizedSourceInput.raw input)
    ((NormalizedSourceInput.raw_satisfiable_iff input).mpr accepted)

theorem value_eq_one (input : List Bool) (accepted : BinaryLanguage.language input) :
    (construct p input).value = 1 :=
  ((construct p input).perfectlyComplete_iff_value_eq_one (alphabet_pos p)).mp
    (perfectlyComplete p input accepted)

end
end PerfectCompleteness.FixedTarget

end

end OAI
