import Mathlib
import OAI.Analysis.MatrixSigning.Machines.MachineTransport
import OAI.Analysis.MatrixSigning.Machines.StackTransfer
import OAI.Analysis.MatrixSigning.Arithmetic.RationalAddPrimitives
import OAI.Analysis.MatrixSigning.Matrices.RowDotRegisters

namespace OAI

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def oneDispatch (_ : Fin 1) (_heads : Fin 29 → Fin 3) (_coin : Bool) : Instruction 29 1 :=
  ⟨none, Vector.ofFn (fun j => if j = 7 then .push true else .stay)⟩
def oneProgram : Program 29 := ofMachine (compile 0 7 7 oneDispatch)

theorem one_spec (s : Fin 29 → List Bool) :
    RunSpec oneProgram s (put s 7 (true :: s 7)) 1 := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin rest =>
      have hr : rest = [] := by simpa using hbits
      subst rest
      refine (KS.W19.MachineTransport.run_ofMachine
        (compile (0 : Fin 1) (7 : Fin 29) 7 oneDispatch)
        (⟨some (0 : Fin 1), s⟩ : Config 29 1) [coin]).trans ?_
      simp only [Machine.run]
      refine (step_compile (0 : Fin 1) (7 : Fin 29) 7 oneDispatch
        (0 : Fin 1) s coin).trans ?_
      change Config.mk none _ = Config.mk none _
      congr 1
      funext j
      by_cases hj : j = 7
      · subst j
        simp [oneDispatch, put, Instruction.action, KS.W29.StackAction.apply]
      · simp [oneDispatch, put, Instruction.action, KS.W29.StackAction.apply, hj]

def incrementPorts : Fin 3 ↪ Fin 29 := ⟨![24, 7, 26], by decide⟩
def incrementAdd : Program 29 := KS.W13.RationalAdd.canonicalAddProgram incrementPorts

def incrementProgram : Program 29 := compose (compose oneProgram incrementAdd)
  (StackTransfer.program 7 24 26)

def incrementTicks (k : ℕ) : ℕ := 1 +
  KS.W13.RationalAdd.canonicalAddTicks (Computability.encodeNat k) [true] +
  (2 * (Computability.encodeNat (k + 1)).length + 2)

theorem increment_spec (s : Fin 29 → List Bool) (k : ℕ)
    (hk : s 24 = Computability.encodeNat k) (h7 : s 7 = []) (h26 : s 26 = []) :
    RunSpec incrementProgram s (put s 24 (Computability.encodeNat (k + 1)))
      (incrementTicks k) := by
  let t := put s 7 [true]
  let u := put (put s 24 []) 7 (Computability.encodeNat (k + 1))
  have h1 : RunSpec oneProgram s t 1 := by simpa [t, h7] using one_spec s
  have hv : KS.W13.RationalAdd.addResult (Computability.encodeNat k) [true] =
      Computability.encodeNat (k + 1) := by
    simp [KS.W13.RationalAdd.addResult, KS.W19.bitsValue_encodeNat, KS.W19.bitsValue,
      KS.W19.digit]
  have h2 : RunSpec incrementAdd t u
      (KS.W13.RationalAdd.canonicalAddTicks (Computability.encodeNat k) [true]) := by
    convert KS.W13.RationalAdd.canonicalAdd_spec incrementPorts s
      (Computability.encodeNat k) [true] using 1 <;> (try rfl) <;>
      funext j <;> fin_cases j <;>
      simp [t, u, put, KS.W19.UnsignedPairSerializer.registers, incrementPorts, hk, h26, hv]
  have h3 := StackTransfer.spec (7 : Fin 29) 24 26 (by decide) (by decide) (by decide) u
    (by simp [u, put, h26])
  have he : StackTransfer.after 7 24 u = put s 24 (Computability.encodeNat (k + 1)) := by
    funext j
    fin_cases j <;> simp [StackTransfer.after, put, u, h7]
  have h := (h1.compose h2).compose h3
  simpa [incrementProgram, incrementTicks, he, u, put] using h

end KS.W12.RowDot

end OAI
