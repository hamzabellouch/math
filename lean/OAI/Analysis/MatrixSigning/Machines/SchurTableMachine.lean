import Mathlib
import OAI.Analysis.MatrixSigning.Machines.SchurDimension
import OAI.Analysis.MatrixSigning.Machines.ProgramTable
import OAI.Analysis.MatrixSigning.Machines.SchurEntryMachine

namespace OAI

section

namespace KS.W07.SchurTableMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def guard (port : Fin 32) (heads : Fin 32 → Fin 3) (_coin : Bool) :
    KS.W29.FixedLoop.GuardInstruction 32 :=
  ⟨if (heads port).val = 0 then .halt else .call,
    Vector.ofFn (fun j => if j=port then .pop else .stay)⟩

def columnIncrementPorts : Fin 3 ↪ Fin 32 := ⟨![0,28,1], by decide⟩
def rowIncrementPorts : Fin 3 ↪ Fin 32 := ⟨![0,27,1], by decide⟩

def columnBody : Program 32 := compose SchurEntryMachine.program
  (SchurCounters.incrementProgram columnIncrementPorts)

def columnLoop : Program 32 := KS.W29.FixedLoop.loop columnBody (guard 25)

def rowBody : Program 32 := compose (SchurDimension.unaryProgram true)
  (compose (SchurCounters.pushProgram 28 true)
    (compose columnLoop (compose (KS.W04.BinaryStackMoves.clearProgram 28)
      (SchurCounters.incrementProgram rowIncrementPorts))))

def rowLoop : Program 32 := KS.W29.FixedLoop.loop rowBody (guard 24)

def «initialize» : Program 32 := compose SchurDimension.predecessor
  (compose (SchurDimension.unaryProgram false) (SchurCounters.pushProgram 27 true))

def finish : Program 32 := compose (KS.W04.BinaryStackMoves.clearProgram 27)
  SchurEntryMachine.finishProgram

def program : Program 32 := compose «initialize» (compose rowLoop finish)

def inputState {n : ℕ} (M : DenseRatMatrix (n+1)) : Fin 32 → List Bool :=
  fun j => if j=31 then KS.W08.denseMatrixTape M else
    if j=26 then Computability.encodeNat (n+1) else []

def outputState {n : ℕ} (M : DenseRatMatrix (n+1)) : Fin 32 → List Bool :=
  fun j => if j=31 then KS.W08.denseMatrixTape M else
    if j=26 then Computability.encodeNat (n+1) else
    if j=30 then Computability.encodeNat n else
    if j=23 then KS.W08.denseMatrixTape
      (DenseRatMatrix.ofMatrix (KS.W17.schurTail (DenseRatMatrix.decode M))) else []

theorem guard_empty (body : Program 32) (port : Fin 32) (s : Fin 32 → List Bool)
    (hs : s port = []) (coin : Bool) :
    (KS.W29.FixedLoop.loop body (guard port)).toMachine.step
      ⟨some (KS.W29.FixedLoop.guardState body),s⟩ coin = ⟨none,s⟩ := by
  rw [KS.W29.FixedLoop.step_guard]
  apply congrArg₂ Config.mk
  · simp [guard,KS.W29.FixedLoop.guardInstruction,observedHeads,hs,KS.W29.topCode]
    rfl
  · funext j
    by_cases hj : j=port
    · subst j; simp [guard,KS.W29.FixedLoop.guardInstruction,observedHeads,hs,KS.W29.topCode,Instruction.action,KS.W29.StackAction.apply]
    · simp [guard,KS.W29.FixedLoop.guardInstruction,observedHeads,hs,KS.W29.topCode,Instruction.action,KS.W29.StackAction.apply,hj]

theorem guard_cons (body : Program 32) (port : Fin 32) (s : Fin 32 → List Bool)
    (count : List Bool) (hs : s port = true :: count) (coin : Bool) :
    (KS.W29.FixedLoop.loop body (guard port)).toMachine.step
      ⟨some (KS.W29.FixedLoop.guardState body),s⟩ coin =
      KS.W29.FixedLoop.liftBody body ⟨some body.initial,Function.update s port count⟩ := by
  rw [KS.W29.FixedLoop.step_guard]
  apply congrArg₂ Config.mk
  · simp [guard,KS.W29.FixedLoop.guardInstruction,observedHeads,hs,KS.W29.topCode]
  · funext j
    by_cases hj : j=port
    · subst j; simp [guard,KS.W29.FixedLoop.guardInstruction,observedHeads,hs,KS.W29.topCode,Instruction.action,KS.W29.StackAction.apply]
    · simp [guard,KS.W29.FixedLoop.guardInstruction,observedHeads,hs,KS.W29.topCode,Instruction.action,KS.W29.StackAction.apply,hj]

theorem table_length : program.table.length = program.states * (3^32*2) := by
  exact KS.W07.compose_table_length «initialize» (compose rowLoop finish)

end KS.W07.SchurTableMachine

end

end OAI
