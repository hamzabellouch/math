import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.MultiplicationMachine
import OAI.Analysis.MatrixSigning.Machines.DeterministicCombinators

namespace OAI

section

namespace KS.W03.MultiplicationDeterministic
open KS.W29.Deterministic

theorem copy_coinIndependent (c : KS.W29.Config 2) (a b : Bool) :
    KS.W29.CopyInput.machine.step c a = KS.W29.CopyInput.machine.step c b := by
  rcases c with ⟨state, workTapes⟩
  cases state with
  | none => rfl
  | some s =>
    simp only [KS.W29.BinaryMachine.step]
    erw [KS.W29.CopyInput.table_lookup, KS.W29.CopyInput.table_lookup]

theorem frame_coinIndependent : ∀ (c : KS.W29.Config 3) (a b : Bool),
    KS.W29.FrameDecoder.machine.step c a = KS.W29.FrameDecoder.machine.step c b :=
  coinIndependent_compile3 0 KS.W29.FrameDecoder.dispatch (fun _ _ _ _ => rfl)

theorem reverse_coinIndependent : ∀ (c : KS.W29.Config 3) (a b : Bool),
    KS.W29.NormalizeOutput.machine.step c a = KS.W29.NormalizeOutput.machine.step c b :=
  coinIndependent_withEntry3 KS.W29.FrameDecoder.machine (2 : Fin 3) frame_coinIndependent

theorem adder_coinIndependent : ∀ (c : KS.W29.Config 2) (a b : Bool),
    KS.W01.BinaryAdder.machine.step c a = KS.W01.BinaryAdder.machine.step c b :=
  coinIndependent_compile3 0 KS.W01.BinaryAdder.dispatch (fun _ _ _ _ => rfl)

theorem trim_coinIndependent : ∀ (c : KS.W29.Config 2) (a b : Bool),
    KS.W19.BinaryTrimMachine.machine.step c a = KS.W19.BinaryTrimMachine.machine.step c b :=
  coinIndependent_compile3 0 KS.W19.BinaryTrimMachine.dispatch (fun _ _ _ _ => rfl)

theorem body_coinIndependent : CoinIndependent KS.W03.MultiplicationBody.body := by
  apply coinIndependent_compose
  · apply coinIndependent_compose
    · apply coinIndependent_compose
      · exact coinIndependent_lift3 _ _ copy_coinIndependent
      · exact coinIndependent_lift3 _ _ adder_coinIndependent
    · exact coinIndependent_lift3 _ _ reverse_coinIndependent
  · exact coinIndependent_compile (0 : Fin 1) (0 : Fin 7) (3 : Fin 7)
      (fun _ _ _ => KS.W03.MultiplicationBody.shiftInstruction) (fun _ _ _ _ => rfl)

theorem loop_coinIndependent : CoinIndependent KS.W03.MultiplicationLoop.program :=
  coinIndependent_loop _ _ body_coinIndependent (fun _ _ _ => rfl)

theorem initialize_coinIndependent : CoinIndependent KS.W03.MultiplicationInitialize.program := by
  apply coinIndependent_compose
  · exact coinIndependent_lift3 _ _ frame_coinIndependent
  · exact coinIndependent_lift3 _ _ frame_coinIndependent

theorem normalize_coinIndependent : CoinIndependent KS.W03.MultiplicationNormalize.program := by
  apply coinIndependent_compose
  · exact coinIndependent_lift3 _ _ reverse_coinIndependent
  · exact coinIndependent_lift3 _ _ trim_coinIndependent

theorem coinIndependent : CoinIndependent KS.W03.MultiplicationMachine.program :=
  coinIndependent_compose _ _
    (coinIndependent_compose _ _ initialize_coinIndependent loop_coinIndependent)
    normalize_coinIndependent

end KS.W03.MultiplicationDeterministic

end

end OAI
