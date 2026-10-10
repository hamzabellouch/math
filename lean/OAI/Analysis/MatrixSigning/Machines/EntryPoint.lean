import Mathlib
import OAI.Analysis.MatrixSigning.Machines.BinaryMachine

namespace OAI

section

namespace KS.W29

def BinaryMachine.withEntry (M : BinaryMachine) (entry : Fin M.states) : BinaryMachine :=
  ⟨M.states, entry, M.table⟩

@[simp] theorem BinaryMachine.withEntry_step (M : BinaryMachine) (entry : Fin M.states)
    (c : Config M.states) (b : Bool) : (M.withEntry entry).step c b = M.step c b := by
  rcases c with ⟨state, «stacks»⟩
  cases state <;> rfl

theorem BinaryMachine.withEntry_run (M : BinaryMachine) (entry : Fin M.states)
    (c : Config M.states) (bits : List Bool) :
    (M.withEntry entry).run c bits = M.run c bits := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      erw [BinaryMachine.run, BinaryMachine.withEntry_step, ih, BinaryMachine.run]

@[simp] theorem BinaryMachine.withEntry_initial (M : BinaryMachine) (entry : Fin M.states) :
    (M.withEntry entry).initial = entry := rfl

@[simp] theorem BinaryMachine.withEntry_init_state (M : BinaryMachine) (entry : Fin M.states)
    (input : List Bool) : ((M.withEntry entry).init input).state = some entry := rfl

@[simp] theorem BinaryMachine.withEntry_init_stacks (M : BinaryMachine) (entry : Fin M.states)
    (input : List Bool) : ((M.withEntry entry).init input).«stacks» = (M.init input).«stacks» := rfl

end KS.W29

end

end OAI
