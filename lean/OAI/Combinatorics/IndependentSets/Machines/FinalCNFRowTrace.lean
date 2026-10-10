import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineLookupDiscard
import OAI.Combinatorics.IndependentSets.Machines.AmbientRelation

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable

def endpointTapes (base : Tape → List Bool) (tail reverse : Nat) (rest : List Bool) :=
  Hastad.SourceMachine.fieldTapes Tape.input Tape.reverseIndex
    (Hastad.SourceMachine.fieldTapes Tape.input Tape.tail base
      (encodeWord reverse ++ rest) (encodeWord tail ++ base .tail))
    rest (encodeWord reverse ++ base .reverseIndex)

def endpointsInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (tail reverse : Nat) (rest : List Bool)
    (hinput : base .input = encodeWord tail ++ encodeWord reverse ++ rest)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .startTail, ((ambient, ()), none), base⟩
      (some ⟨some .headTableFirst, ((ambient, ()), none),
        endpointTapes base tail reverse rest⟩) (tail + reverse + 4) := by
  let first := Hastad.SourceMachine.fieldTapes Tape.input Tape.tail base
    (encodeWord reverse ++ rest) (encodeWord tail ++ base .tail)
  let run₁ := Hastad.SourceMachine.fieldInTime Tape.input Tape.tail (by decide)
    .startTail .readTail (some .startReverse) (program headerPlan plan) rfl rfl
    base tail (encodeWord reverse ++ rest) (by simpa only [List.append_assoc] using hinput)
    (ambient, ()) none
  have input₁ : first .input = encodeWord reverse ++ rest := by
    simp [first, Hastad.SourceMachine.fieldTapes]
  have reverse₁ : first .reverseIndex = base .reverseIndex := by
    simp [first, Hastad.SourceMachine.fieldTapes]
  let run₂ := Hastad.SourceMachine.fieldInTime Tape.input Tape.reverseIndex (by decide)
    .startReverse .readReverse (some .headTableFirst) (program headerPlan plan) rfl rfl
    first reverse rest input₁ (ambient, ()) none
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  simpa only [first, reverse₁, endpointTapes, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using joined

def relationInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (relation : GraphTables.RelationTable) (rest : List Bool)
    (hinput : base .input = encodeWords (GraphTables.relationWords relation) ++ rest)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .readRelation, ((ambient, ()), none), base⟩
      (some ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((((), fun i => relation[i]), ()), none), Function.update base .input rest⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .readRelation) _ _) = _
    rw [program, stepAux_readRelationAt _ _ _ _ _ _ _ _ _ hinput]
  steps_le_m := Nat.le_refl _

def emitInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (operands : Fin 5 → Nat) (hoperands : ∀ i, base (source i) = encodeWord (operands i))
    (hscratch : base .scratch = []) (ambient : Ambient)
    (N : Nat) (hbounded : ∀ i, operands i ≤ N) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((ambient, ()), none), base⟩
      (some ⟨some .clearTail, ((ambient, ()), none),
        Function.update base .accumulator
          ((plan.flatMap (Emitter.commandBits operands ambient)).reverse ++ base .accumulator)⟩)
      (plan.length * (3 * (N + 1) + 3) + 1) := by
  have run := Emitter.planInTime (Emitter.listCommands plan)
    source Tape.scratch Tape.accumulator source_ne_scratch source_ne_accumulator (by decide)
    Label.row (some .clearTail) (program headerPlan plan) (fun _ => rfl)
    operands base hoperands hscratch ambient N hbounded
  simpa only [Emitter.bits_listCommands, Emitter.resultTapes] using run

def finishTapes (base : Tape → List Bool) (row : Nat) : Tape → List Bool :=
  Function.update
    (Function.update (Function.update (Function.update base Tape.tail []) Tape.head [])
      Tape.reverseIndex []) Tape.rowIndex (encodeWord (row + 1))

def finishInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (tail head reverse row : Nat)
    (htail : base .tail = encodeWord tail) (hhead : base .head = encodeWord head)
    (hreverse : base .reverseIndex = encodeWord reverse)
    (hrow : base .rowIndex = encodeWord row) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .clearTail, ((ambient, ()), none), base⟩
      (some ⟨some .guard, ((ambient, ()), none), finishTapes base row⟩)
      (tail + head + reverse + 4) := by
  let t₁ := Function.update base Tape.tail []
  let t₂ := Function.update t₁ Tape.head []
  let t₃ := Function.update t₂ Tape.reverseIndex []
  let run₁ := MachineLookup.discardInTime Tape.tail .clearTail .clearHead
    (program headerPlan plan) rfl base tail [] (by simpa using htail) (ambient, ()) none
  have hhead₁ : t₁ .head = encodeWord head := by simp [t₁, hhead]
  let run₂ := MachineLookup.discardInTime Tape.head .clearHead .clearReverse
    (program headerPlan plan) rfl t₁ head [] (by simpa using hhead₁) (ambient, ()) none
  have hreverse₂ : t₂ .reverseIndex = encodeWord reverse := by simp [t₂, t₁, hreverse]
  let run₃ := MachineLookup.discardInTime Tape.reverseIndex .clearReverse .nextRow
    (program headerPlan plan) rfl t₂ reverse [] (by simpa using hreverse₂) (ambient, ()) none
  let run₄ : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .nextRow, ((ambient, ()), none), t₃⟩
      (some ⟨some .guard, ((ambient, ()), none), finishTapes base row⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program headerPlan plan .nextRow) _ _) = _
      simp only [program, TM2.stepAux]
      congr 2
      simp [t₃, t₂, t₁, finishTapes, hrow, encodeWord, List.replicate_succ]
    steps_le_m := Nat.le_refl _ }
  let r₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let r₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂ run₃
  have run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃ run₄
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using run

end IndependentSetsGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
