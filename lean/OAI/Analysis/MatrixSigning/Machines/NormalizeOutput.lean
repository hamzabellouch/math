import Mathlib
import OAI.Analysis.MatrixSigning.Machines.Sequential
import OAI.Analysis.MatrixSigning.Machines.EntryPoint
import OAI.Analysis.MatrixSigning.Encoding.FrameDecoder

namespace OAI

section

namespace KS.W29
namespace NormalizeOutput

def machine : BinaryMachine := FrameDecoder.machine.withEntry (2 : Fin 3)

theorem run_normalize (input output scratch bits : List Bool)
    (h : bits.length = scratch.length + 1) :
    machine.run (FrameDecoder.config (some 2) input output scratch) bits =
      FrameDecoder.config none input (scratch.reverse ++ output) [] := by
  unfold machine
  erw [BinaryMachine.withEntry_run]
  exact FrameDecoder.run_reverse input output scratch bits h

theorem initial_eq : machine.initial = (2 : Fin 3) := rfl

theorem run_reversed (input result bits : List Bool) (h : bits.length = result.length + 1) :
    machine.run (FrameDecoder.config (some machine.initial) input [] result.reverse) bits =
      FrameDecoder.config none input result [] := by
  rw [initial_eq, run_normalize]
  · simp
    rfl
  · simpa using h

theorem compose_result (M : BinaryMachine) (c : Config M.states)
    (first second input result : List Bool)
    (hfirst : Sequential.HaltsAfter M c first)
    (hstack : (M.run c first).«stacks» =
      (FrameDecoder.config (some machine.initial) input [] result.reverse).«stacks»)
    (hsecond : second.length = result.length + 1) :
    (Sequential.compose M machine).run (Sequential.liftLeft M machine c) (first ++ second) =
      Sequential.liftRight M machine (FrameDecoder.config none input result []) := by
  rw [Sequential.run_compose M machine c first second hfirst]
  have hc : (⟨some machine.initial, (M.run c first).«stacks»⟩ : Config machine.states) =
      FrameDecoder.config (some machine.initial) input [] result.reverse := by
    rw [hstack]
    rfl
  rw [hc, run_reversed input result second hsecond]

end NormalizeOutput
end KS.W29

end

end OAI
