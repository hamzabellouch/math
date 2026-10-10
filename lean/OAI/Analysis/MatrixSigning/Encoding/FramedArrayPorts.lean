import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedStackPortLift
import OAI.Analysis.MatrixSigning.Encoding.FramedArrayRetrieval

namespace OAI

namespace KS.W11.FramedArray
open KS.W01.FixedStack
open KS.W29.FixedSequential

def liftedLookup {k : ℕ} (ports : Fin 4 ↪ Fin k) : Program k :=
  KS.W29.FixedSequential.liftPorts lookupProgram ports

theorem liftedLookup_states {k : ℕ} (ports : Fin 4 ↪ Fin k) :
    (liftedLookup ports).states = 6 := rfl

theorem run_lookup_ports {k : ℕ} (ports : Fin 4 ↪ Fin k)
    (xs : List (List Bool)) (i : ℕ) (hi : i < xs.length) (tail bits : List Bool)
    (c : Config k lookupProgram.states)
    (hc : projectPorts ports c =
      config (some lookupProgram.initial) (xs.flatMap KS.W01.frame ++ tail)
        [] [] (List.replicate i true))
    (hlen : 2 * (xs.flatMap KS.W01.frame ++ tail).length + i + 1 ≤ bits.length) :
    let result := (liftedLookup ports).toMachine.run c bits
    result.state = none ∧
      result.«stacks» (ports 0) = (xs.drop (i + 1)).flatMap KS.W01.frame ++ tail ∧
      result.«stacks» (ports 1) = xs[i] ∧
      result.«stacks» (ports 2) = [] ∧
      result.«stacks» (ports 3) = [] ∧
      ∀ j, (∀ r, j ≠ ports r) → result.«stacks» j = c.«stacks» j := by
  have hp := KS.W01.FixedStack.liftPorts_project_run lookupProgram.toMachine ports c bits
  erw [hc, run_lookup xs i hi tail bits hlen] at hp
  refine ⟨congrArg (fun d : Config 4 lookupProgram.states => d.state) hp,
    congrArg (fun d : Config 4 lookupProgram.states => d.«stacks» 0) hp,
    congrArg (fun d : Config 4 lookupProgram.states => d.«stacks» 1) hp,
    congrArg (fun d : Config 4 lookupProgram.states => d.«stacks» 2) hp,
    congrArg (fun d : Config 4 lookupProgram.states => d.«stacks» 3) hp, ?_⟩
  intro j hj
  exact KS.W01.FixedStack.liftPorts_run_preserves_other lookupProgram.toMachine ports c bits j hj

theorem lookup_ports_linear_time {k : ℕ} (ports : Fin 4 ↪ Fin k)
    (xs : List (List Bool)) (i : ℕ) (hi : i < xs.length) (tail : List Bool)
    (c : Config k lookupProgram.states)
    (hc : projectPorts ports c =
      config (some lookupProgram.initial) (xs.flatMap KS.W01.frame ++ tail)
        [] [] (List.replicate i true)) :
    HaltsFromWithin (liftedLookup ports) c
      (2 * (xs.flatMap KS.W01.frame ++ tail).length + i + 1) := by
  intro bits hlen
  exact (run_lookup_ports ports xs i hi tail bits c hc hlen.ge).1

end KS.W11.FramedArray

end OAI
