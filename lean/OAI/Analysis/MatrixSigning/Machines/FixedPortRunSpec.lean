import Mathlib
import OAI.Analysis.MatrixSigning.Machines.MachineCombinators
import OAI.Analysis.MatrixSigning.Machines.FixedStackPortLift

namespace OAI

section

namespace KS.W01.FixedStack

theorem liftPorts_run_eq {K : ℕ} (M : Machine) (ports : Fin M.stackCount ↪ Fin K)
    (c : Config K M.states) (bits : List Bool) (out : Fin K → List Bool)
    (h : M.run (projectPorts ports c) bits = ⟨none, fun i => out (ports i)⟩)
    (hother : ∀ j, (∀ i, j ≠ ports i) → out j = c.«stacks» j) :
    (liftPorts M ports).run c bits = ⟨none, out⟩ := by
  have hp := liftPorts_project_run M ports c bits
  rw [h] at hp
  have hs : ((liftPorts M ports).run c bits).state = none :=
    congrArg (fun d : Config M.stackCount M.states => d.state) hp
  have ht : ((liftPorts M ports).run c bits).«stacks» = out := by
    funext j
    by_cases hj : ∃ i, j = ports i
    · obtain ⟨i, rfl⟩ := hj
      exact congrArg (fun d : Config M.stackCount M.states => d.«stacks» i) hp
    · have hn : ∀ i, j ≠ ports i := by simpa only [not_exists] using hj
      rw [liftPorts_run_preserves_other M ports c bits j hn, hother j hn]
  exact congrArg₂ Config.mk hs ht

end KS.W01.FixedStack

namespace KS.W01.FixedPortRunSpec
open KS.W01.FixedStack (Config projectPorts)
open KS.W29.FixedSequential (Program)
open KS.W03.MachineCombinators (RunSpec)

theorem lift_runSpec {k K : ℕ} (P : Program k) (ports : Fin k ↪ Fin K)
    (before after : Fin k → List Bool) (largeBefore largeAfter : Fin K → List Bool)
    (ticks : ℕ) (h : RunSpec P before after ticks)
    (hbefore : ∀ i, largeBefore (ports i) = before i)
    (hafter : ∀ i, largeAfter (ports i) = after i)
    (hother : ∀ j, (∀ i, j ≠ ports i) → largeAfter j = largeBefore j) :
    RunSpec (KS.W29.FixedSequential.liftPorts P ports) largeBefore largeAfter ticks := by
  intro bits hbits
  change (KS.W01.FixedStack.liftPorts P.toMachine ports).run
    ⟨some P.initial, largeBefore⟩ bits = ⟨none, largeAfter⟩
  apply KS.W01.FixedStack.liftPorts_run_eq
  · have hi : projectPorts ports (⟨some P.initial, largeBefore⟩ : Config K P.states) =
        ⟨some P.initial, before⟩ := by
      change Config.mk (some P.initial) (fun i => largeBefore (ports i)) =
        Config.mk (some P.initial) before
      exact congrArg (Config.mk (some P.initial)) (funext hbefore)
    erw [hi, h bits hbits]
    congr 1
    funext i
    exact (hafter i).symm
  · exact hother

end KS.W01.FixedPortRunSpec

end

end OAI
