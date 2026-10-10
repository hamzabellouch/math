import Mathlib
import OAI.Computability.MinUncut.Machines.PoweringMachineGlobal

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.PoweringRuntimeBudget

open Turing

theorem stackLength_le_of_execution (tm : FinTM2) (start finish : tm.Cfg)
    (initialBound priorBudget : Nat)
    (initial : ∀ k, (start.stk k).length ≤ initialBound)
    (prior : StateTransition.EvalsToInTime tm.step start (some finish) priorBudget)
    (k : tm.K) :
    (finish.stk k).length ≤ initialBound + priorBudget * Runtime.programPushBound tm := by
  have grown := Runtime.executionSizeBound tm.step (fun cfg => (cfg.stk k).length)
    (Runtime.programPushBound tm) (Runtime.stepStackLength tm k) prior
  exact grown.trans (Nat.add_le_add_right (initial k) _)

theorem stackLength_le_from_input (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (finish : tm.Cfg) (priorBudget : Nat)
    (prior : StateTransition.EvalsToInTime tm.step (initList tm input)
      (some finish) priorBudget) (k : tm.K) :
    (finish.stk k).length ≤ input.length + priorBudget * Runtime.programPushBound tm :=
  stackLength_le_of_execution tm (initList tm input) finish input.length priorBudget
    (Runtime.initialStackLength tm input) prior k

abbrev tapeCount (radius : Nat) : Nat :=
  4 + (11 + PoweringMachineRowBody.capacity radius + 1)

theorem finish_steps_le_of_execution (d radius : Nat) (input : List Bool)
    (before : (PoweringMachineGlobal.machine d radius).Cfg)
    (priorBudget vertices darts : Nat)
    (prior : StateTransition.EvalsToInTime (PoweringMachineGlobal.machine d radius).step
      (initList (PoweringMachineGlobal.machine d radius) input) (some before) priorBudget) :
    PoweringMachineFinish.steps (PoweringMachineGlobal.enumeration radius)
      (PoweringMachineGlobal.outputTape radius) before.stk vertices darts ≤
      2 * (vertices + darts) + 6 + tapeCount radius *
        (input.length + priorBudget * Runtime.programPushBound
          (PoweringMachineGlobal.machine d radius) + vertices + darts + 3) := by
  exact PoweringMachineFinish.steps_le_uniform (PoweringMachineGlobal.enumeration radius)
    (PoweringMachineGlobal.outputTape radius) before.stk vertices darts
    (input.length + priorBudget * Runtime.programPushBound (PoweringMachineGlobal.machine d radius))
    (stackLength_le_from_input (PoweringMachineGlobal.machine d radius) input before priorBudget prior)

theorem total_steps_le_of_execution (d radius : Nat) (input : List Bool)
    (before : (PoweringMachineGlobal.machine d radius).Cfg)
    (priorBudget vertices darts : Nat)
    (prior : StateTransition.EvalsToInTime (PoweringMachineGlobal.machine d radius).step
      (initList (PoweringMachineGlobal.machine d radius) input) (some before) priorBudget) :
    prior.steps + PoweringMachineFinish.steps (PoweringMachineGlobal.enumeration radius)
      (PoweringMachineGlobal.outputTape radius) before.stk vertices darts ≤
      priorBudget + (2 * (vertices + darts) + 6 + tapeCount radius *
        (input.length + priorBudget * Runtime.programPushBound
          (PoweringMachineGlobal.machine d radius) + vertices + darts + 3)) :=
  Nat.add_le_add prior.steps_le_m
    (finish_steps_le_of_execution d radius input before priorBudget vertices darts prior)

end MinUncutGames.Foundations.Complexity.PoweringRuntimeBudget

end

end OAI
