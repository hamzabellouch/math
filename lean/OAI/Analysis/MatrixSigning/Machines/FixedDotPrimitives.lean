import Mathlib
import OAI.Analysis.MatrixSigning.Machines.StackTransfer
import OAI.Analysis.MatrixSigning.Machines.FixedDotControl
import OAI.Analysis.MatrixSigning.Arithmetic.RationalMultiplicationMachine

namespace OAI

section

namespace KS.W12.FixedDot

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def initialPorts (n : ℕ) (hn : n ≤ 19) : Fin n ↪ Fin 19 where
  toFun i := ⟨i.val, lt_of_lt_of_le i.isLt hn⟩
  inj' := fun _ _ h => Fin.ext (congrArg (fun j : Fin 19 => j.val) h)

def multiplyProgram : Program 19 :=
  KS.W29.FixedSequential.liftPorts KS.W15.RationalMultiply.program (initialPorts 13 (by decide))

theorem multiplication_spec (rem acc : List Bool) (p : ℚ × ℚ) :
    RunSpec multiplyProgram (registers rem (pairPayload p) [] acc [])
      (registers rem [] (KS.W01.encodeRat (p.1 * p.2)) acc [])
      (KS.W15.RationalMultiply.totalTicks p.1 p.2) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (KS.W15.RationalMultiply.full_spec p.1 p.2)
  · intro i
    fin_cases i <;> rfl
  · intro i
    fin_cases i <;> rfl
  · intro j hj
    have h0 : j ≠ 0 := hj 0
    have h10 : j ≠ 10 := hj 10
    simp [registers, h0, h10]

def framePorts : Fin 3 ↪ Fin 19 where
  toFun i := if i = 0 then 16 else if i = 1 then 0 else 18
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def decodeProgram : Program 19 := ofMachine (lift3 KS.W29.FrameDecoder.machine framePorts)

theorem decode_spec (payload rem acc : List Bool) :
    RunSpec decodeProgram (registers (KS.W01.frame payload ++ rem) [] [] acc [])
      (registers rem payload [] acc []) (3 * payload.length + 2) := by
  intro bits hbits
  refine (KS.W19.MachineTransport.run_ofMachine
    (lift3 KS.W29.FrameDecoder.machine framePorts)
    (⟨some (0 : Fin 3), registers (KS.W01.frame payload ++ rem) [] [] acc []⟩ : Config 19 3)
    bits).trans ?_
  apply lift3_run_eq
  · have hp : project framePorts
        (⟨some 0, registers (KS.W01.frame payload ++ rem) [] [] acc []⟩ : Config 19 3) =
        KS.W29.FrameDecoder.machine.init (KS.W01.frame payload ++ rem) := by
      change KS.W29.Config.mk (some (0 : Fin 3)) _ =
        KS.W29.Config.mk (some (0 : Fin 3)) _
      congr 1
      funext i
      fin_cases i <;> rfl
    refine (congrArg (fun c : KS.W29.Config 3 => KS.W29.FrameDecoder.machine.run c bits)
      hp).trans ((KS.W29.FrameDecoder.run_frame_of_length_ge payload rem bits hbits.ge).trans ?_)
    change KS.W29.Config.mk none _ = KS.W29.Config.mk none _
    congr 1
    funext i
    fin_cases i <;> rfl
  · intro j hj
    have h16 : j ≠ 16 := hj 0
    have h0 : j ≠ 0 := hj 1
    have h18 : j ≠ 18 := hj 2
    simp [registers, h16, h0, h18]

def transferProgram (source target : Fin 19) : Program 19 :=
  compose (KS.W04.BinaryStackMoves.moveProgram source 18)
    (KS.W04.BinaryStackMoves.moveProgram 18 target)

def transferAfter (source target : Fin 19) (before : Fin 19 → List Bool) : Fin 19 → List Bool :=
  fun j => if j = source then [] else if j = target then before source ++ before target else before j

theorem transfer_spec (source target : Fin 19) (hst : source ≠ target)
    (hs : source ≠ 18) (ht : target ≠ 18)
    (before : Fin 19 → List Bool) (htmp : before 18 = []) :
    RunSpec (transferProgram source target) before (transferAfter source target before)
      (2 * (before source).length + 2) := by
  exact KS.W12.StackTransfer.spec source target 18 hst hs ht before htmp

end KS.W12.FixedDot

end

end OAI
