import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineUnaryEqualityBit
import OAI.Combinatorics.IndependentSets.Machines.Block
import OAI.Combinatorics.IndependentSets.Machines.PoweringMachineLoop

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineLoop
open Turing

variable {K Λ σ : Type} [DecidableEq K]

def rowBase (output : K) (base : K → List Bool)
    (rowBlock : Nat → List Bool) (n r : Nat) : K → List Bool :=
  Function.update base output (remainingRows rowBlock n r ++ base output)

def VertexBodyTraces (counter output : K) (guardLabel bodyLabel : Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (rowBlock : Nat → List Bool) (cost : Nat → Nat) (n : Nat) : Prop :=
  ∀ r, r < n → ∀ accumulator : List Bool,
    (MachineComposition.advance (TM2.step program))^[cost r]
      (some ⟨some bodyLabel, (ambient, none),
        MachineUnaryCounter.counterTapes counter
          (Function.update base output accumulator) r suffix⟩) =
      some ⟨some guardLabel, (ambient, none),
        MachineUnaryCounter.counterTapes counter
          (Function.update base output (rowBlock r ++ accumulator)) r suffix⟩

theorem vertexBodyTraces_to_counted (counter output : K) (guardLabel bodyLabel : Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (rowBlock : Nat → List Bool) (cost : Nat → Nat) (n : Nat)
    (bodies : VertexBodyTraces counter output guardLabel bodyLabel program
      base suffix ambient rowBlock cost n) :
    MachineCountedLoop.BodyTraces counter guardLabel bodyLabel program suffix
      (fun _ => ambient) (fun _ => none) (rowBase output base rowBlock n) cost n := by
  intro r hr
  have h := bodies r hr (remainingRows rowBlock n (r + 1) ++ base output)
  simpa only [MachineCountedLoop.bodyConfiguration, MachineCountedLoop.guardConfiguration,
    rowBase, remainingRows_step rowBlock n r hr, List.append_assoc] using h

def vertexLoopInTime (counter output : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atGuard : program guardLabel = MachineUnaryCounter.guard counter bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (rowBlock : Nat → List Bool) (cost : Nat → Nat) (n bodyBound : Nat)
    (bodies : VertexBodyTraces counter output guardLabel bodyLabel program
      base suffix ambient rowBlock cost n)
    (bounded : ∀ r, r < n → cost r ≤ bodyBound) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, (ambient, none),
        MachineUnaryCounter.counterTapes counter base n suffix⟩
      (some ⟨some exitLabel, (ambient, none),
        MachineUnaryCounter.counterTapes counter
          (rowBase output base rowBlock n 0) 0 suffix⟩)
      (n * (bodyBound + 1) + 1) := by
  have h := MachineCountedLoop.loopInTime counter guardLabel bodyLabel exitLabel
    program atGuard suffix (fun _ => ambient) (fun _ => none)
    (rowBase output base rowBlock n) cost n bodyBound
    (vertexBodyTraces_to_counted counter output guardLabel bodyLabel program
      base suffix ambient rowBlock cost n bodies) bounded
  simpa [MachineCountedLoop.guardConfiguration, MachineCountedLoop.exitConfiguration,
    rowBase] using h

theorem vertexLoop_output (counter output : K) (different : output ≠ counter)
    (base : K → List Bool) (suffix : List Bool) (rowBlock : Nat → List Bool) (n : Nat) :
    MachineUnaryCounter.counterTapes counter (rowBase output base rowBlock n 0) 0 suffix output =
      remainingRows rowBlock n 0 ++ base output := by
  simp [MachineUnaryCounter.counterTapes, rowBase, different]

def varyingRowBase (output : K) (base : Nat → K → List Bool)
    (rowBlock : Nat → List Bool) (n r : Nat) : K → List Bool :=
  Function.update (base r) output (remainingRows rowBlock n r ++ base n output)

def VaryingVertexBodyTraces (counter output : K) (guardLabel bodyLabel : Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (base : Nat → K → List Bool) (suffix : List Bool) (ambient : Nat → σ)
    (rowBlock : Nat → List Bool) (cost : Nat → Nat) (n : Nat) : Prop :=
  ∀ r, r < n → ∀ accumulator : List Bool,
    (MachineComposition.advance (TM2.step program))^[cost r]
      (some ⟨some bodyLabel, (ambient (r + 1), none),
        MachineUnaryCounter.counterTapes counter
          (Function.update (base (r + 1)) output accumulator) r suffix⟩) =
      some ⟨some guardLabel, (ambient r, none),
        MachineUnaryCounter.counterTapes counter
          (Function.update (base r) output (rowBlock r ++ accumulator)) r suffix⟩

theorem varyingVertexBodyTraces_to_counted (counter output : K) (guardLabel bodyLabel : Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (base : Nat → K → List Bool) (suffix : List Bool) (ambient : Nat → σ)
    (rowBlock : Nat → List Bool) (cost : Nat → Nat) (n : Nat)
    (bodies : VaryingVertexBodyTraces counter output guardLabel bodyLabel program
      base suffix ambient rowBlock cost n) :
    MachineCountedLoop.BodyTraces counter guardLabel bodyLabel program suffix
      ambient (fun _ => none) (varyingRowBase output base rowBlock n) cost n := by
  intro r hr
  have h := bodies r hr (remainingRows rowBlock n (r + 1) ++ base n output)
  simpa only [MachineCountedLoop.bodyConfiguration, MachineCountedLoop.guardConfiguration,
    varyingRowBase, remainingRows_step rowBlock n r hr, List.append_assoc] using h

def vertexLoopInTime_varying (counter output : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atGuard : program guardLabel = MachineUnaryCounter.guard counter bodyLabel exitLabel)
    (base : Nat → K → List Bool) (suffix : List Bool) (ambient : Nat → σ)
    (rowBlock : Nat → List Bool) (cost : Nat → Nat) (n bodyBound : Nat)
    (bodies : VaryingVertexBodyTraces counter output guardLabel bodyLabel program
      base suffix ambient rowBlock cost n)
    (bounded : ∀ r, r < n → cost r ≤ bodyBound) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, (ambient n, none),
        MachineUnaryCounter.counterTapes counter (base n) n suffix⟩
      (some ⟨some exitLabel, (ambient 0, none),
        MachineUnaryCounter.counterTapes counter
          (varyingRowBase output base rowBlock n 0) 0 suffix⟩)
      (n * (bodyBound + 1) + 1) := by
  have h := MachineCountedLoop.loopInTime counter guardLabel bodyLabel exitLabel
    program atGuard suffix ambient (fun _ => none)
    (varyingRowBase output base rowBlock n) cost n bodyBound
    (varyingVertexBodyTraces_to_counted counter output guardLabel bodyLabel program
      base suffix ambient rowBlock cost n bodies) bounded
  simpa [MachineCountedLoop.guardConfiguration, MachineCountedLoop.exitConfiguration,
    varyingRowBase] using h

theorem vertexLoop_varying_output (counter output : K) (different : output ≠ counter)
    (base : Nat → K → List Bool) (suffix : List Bool)
    (rowBlock : Nat → List Bool) (n : Nat) :
    MachineUnaryCounter.counterTapes counter
        (varyingRowBase output base rowBlock n 0) 0 suffix output =
      remainingRows rowBlock n 0 ++ base n output := by
  simp [MachineUnaryCounter.counterTapes, varyingRowBase, different]

end IndependentSetsGames.Foundations.Complexity.PoweringMachineLoop
namespace IndependentSetsGames.Foundations.Complexity.PoweringMasterState

open Turing
open MachineFixedBlockMap

abbrev OtherRegisters (N : Nat) := Buffer N × (Bool × Option Bool)
abbrev Master (N : Nat) := OtherRegisters N × Option Bool
abbrev CompareState (N : Nat) := Buffer N × (Bool × (Option Bool × Option Bool))
abbrev RowState (N : Nat) := (Bool × (Option Bool × Option Bool)) × Buffer N

def compareEquiv (N : Nat) : Master N ≃ CompareState N :=
  (MachineUnaryEqualityBit.compareStateEquiv (Buffer N)).symm

def rowEquiv (N : Nat) : Master N ≃ RowState N where
  toFun state := ((state.1.2.1, (state.1.2.2, state.2)), state.1.1)
  invFun state := ((state.2, (state.1.1, state.1.2.1)), state.1.2.2)
  left_inv := by rintro ⟨⟨buffer, ⟨flag, left⟩⟩, right⟩; rfl
  right_inv := by rintro ⟨⟨flag, ⟨left, right⟩⟩, buffer⟩; rfl

@[simp] theorem compareEquiv_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    compareEquiv N ((buffer, (flag, left)), right) = (buffer, (flag, (left, right))) := rfl

@[simp] theorem compareEquiv_symm_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    (compareEquiv N).symm (buffer, (flag, (left, right))) = ((buffer, (flag, left)), right) := rfl

@[simp] theorem rowEquiv_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    rowEquiv N ((buffer, (flag, left)), right) = ((flag, (left, right)), buffer) := rfl

@[simp] theorem rowEquiv_symm_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    (rowEquiv N).symm ((flag, (left, right)), buffer) = ((buffer, (flag, left)), right) := rfl

def withBuffer {N : Nat} (buffer : Buffer N) : Master N :=
  ((buffer, (false, none)), none)

def clean (N : Nat) : Master N := withBuffer (emptyBuffer N)

@[simp] theorem equalityBit_clean {N : Nat} (buffer : Buffer N) :
    MachineUnaryEqualityBit.clean buffer = withBuffer buffer := rfl

@[simp] theorem rowEquiv_withBuffer {N : Nat} (buffer : Buffer N) :
    rowEquiv N (withBuffer buffer) = ((false, (none, none)), buffer) := rfl

@[simp] theorem compareEquiv_withBuffer {N : Nat} (buffer : Buffer N) :
    compareEquiv N (withBuffer buffer) = (buffer, (false, (none, none))) := rfl

def clearBuffer {N : Nat} (state : Master N) : Master N :=
  (rowEquiv N).symm ((rowEquiv N state).1, emptyBuffer N)

@[simp] theorem clearBuffer_apply {N : Nat} (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    clearBuffer ((buffer, (flag, left)), right) =
      ((emptyBuffer N, (flag, left)), right) := rfl

@[simp] theorem clearBuffer_withBuffer {N : Nat} (buffer : Buffer N) :
    clearBuffer (withBuffer buffer) = clean N := rfl

end IndependentSetsGames.Foundations.Complexity.PoweringMasterState

end OAI
