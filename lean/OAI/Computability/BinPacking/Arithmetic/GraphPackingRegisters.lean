import OAI.Computability.BinPacking.Machines.PackingJobLoop
import OAI.Computability.BinPacking.Machines.PackingSetupGraph

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingRegisters

open PackingItemExpression PackingInventoryDescriptors
open PackingMachineLayout PackingRegisterFrame

def parameters (fixed : InventoryData) (K : Nat) : PackingSetupExpression.Parameters :=
  ⟨fixed.P, K, fixed.d, fixed.tPlus, fixed.tMinus⟩

inductive Work
  | leftEndpoint | rightEndpoint | leftPower | rightPower
  | counter | one | temporary | reverse | geometryFactor | header
  deriving DecidableEq

instance : Fintype Work where
  elems := {.leftEndpoint, .rightEndpoint, .leftPower, .rightPower, .counter,
    .one, .temporary, .reverse, .geometryFactor, .header}
  complete w := by cases w <;> simp

inductive Extra
  | input | scanScratch | scanTemporary | threshold | endpoints | vertices | edges
  | vertexCounter | edgeCounter | repetitionCounter | poolCounter | powerCounter
  | decodeScratch | reverseOutput | output
  deriving DecidableEq

instance : Fintype Extra where
  elems := {.input, .scanScratch, .scanTemporary, .threshold, .endpoints,
    .vertices, .edges, .vertexCounter, .edgeCounter, .repetitionCounter,
    .poolCounter, .powerCounter, .decodeScratch, .reverseOutput, .output}
  complete e := by cases e <;> simp

abbrev Numerator (fixed : InventoryData) := PackingDescriptorExpression.numerator fixed
abbrev Other (fixed : InventoryData) (K : Nat) := PackingSetupMachine.Reg (parameters fixed K) ⊕ Work
abbrev Register (fixed : InventoryData) (K : Nat) :=
  PackingMachineLayout.Reg (Numerator fixed) denominator (Other fixed K)
abbrev Tape (fixed : InventoryData) (K : Nat) :=
  PackingMachineLayout.Tape (Numerator fixed) denominator (Other fixed K) Extra

def slots (fixed : InventoryData) (K : Nat) :
    (Register fixed K ⊕ Fin 6) ↪ Tape fixed K := registers (Numerator fixed) denominator

def item (fixed : InventoryData) (K : Nat) : Variable ↪ Register fixed K :=
  inputs (Numerator fixed) denominator

def setup (fixed : InventoryData) (K : Nat) :
    PackingSetupMachine.Reg (parameters fixed K) ↪ Register fixed K :=
  (Function.Embedding.inl : PackingSetupMachine.Reg (parameters fixed K) ↪ Other fixed K).trans
    (others (Numerator fixed) denominator)

def work (fixed : InventoryData) (K : Nat) : Work ↪ Register fixed K :=
  (Function.Embedding.inr : Work ↪ Other fixed K).trans
    (others (Numerator fixed) denominator)

def input (fixed : InventoryData) (K : Nat) (i : PackingSetupExpression.Input) : Register fixed K :=
  setup fixed K (PackingSetupMachine.input (parameters fixed K) i)

def output (fixed : InventoryData) (K : Nat) (o : PackingSetupExpression.Output) : Register fixed K :=
  setup fixed K (PackingSetupMachine.output (parameters fixed K) o)

def setupSlots (fixed : InventoryData) (K : Nat) :
    (PackingSetupMachine.Reg (parameters fixed K) ⊕ Fin 6) ↪ Tape fixed K :=
  localSlots (slots fixed K) (setup fixed K)

def graphSlots (fixed : InventoryData) (K : Nat) : Fin 7 ↪ Tape fixed K where
  toFun := ![.inr .input, .inr .scanScratch, .inr .scanTemporary,
    .inr .threshold, .inr .endpoints, .inr .vertices, .inr .edges]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

inductive CountSource
  | input (i : PackingSetupExpression.Input)
  | output (o : PackingSetupExpression.Output)
  | endpoint (right : Bool)
  deriving DecidableEq, Fintype

def countRegister (fixed : InventoryData) (K : Nat) : CountSource → Register fixed K
  | .input i => input fixed K i
  | .output o => output fixed K o
  | .endpoint right => work fixed K (if right then .rightEndpoint else .leftEndpoint)

def tallyRegisters (fixed : InventoryData) (K : Nat) (source : CountSource) :
    BinaryToTallyMachine.Reg ↪ Register fixed K where
  toFun
    | .source => countRegister fixed K source
    | .counter => work fixed K .counter
    | .one => work fixed K .one
    | .temporary => work fixed K .temporary
  inj' := by
    intro a b h
    cases source with
    | input i =>
        cases a <;> cases b <;>
          simp_all [countRegister, input, setup, work, others, PackingSetupMachine.input]
    | output o =>
        cases a <;> cases b <;>
          simp_all [countRegister, output, setup, work, others, PackingSetupMachine.output]
    | endpoint right =>
        cases right <;> cases a <;> cases b <;>
          simp_all [countRegister, work, others]

def tallySlots (fixed : InventoryData) (K : Nat) (source : CountSource) :
    (BinaryToTallyMachine.Reg ⊕ Fin 6) ↪ Tape fixed K :=
  localSlots (slots fixed K) (tallyRegisters fixed K source)

theorem tally_outside (fixed : InventoryData) (K : Nat) (source : CountSource)
    (tape : Extra) (i : BinaryToTallyMachine.Reg ⊕ Fin 6) :
    tallySlots fixed K source i ≠ Sum.inr tape := by
  simp [tallySlots, localSlots, slots, registers]

def endpointRegisters (fixed : InventoryData) (K : Nat) (right : Bool) :
    Fin 7 ↪ Register fixed K where
  toFun := ![countRegister fixed K (.endpoint right), output fixed K .three,
    work fixed K (if right then .rightPower else .leftPower), work fixed K .counter,
    work fixed K .one, work fixed K .temporary, work fixed K .reverse]
  inj' := by
    intro i j h
    cases right <;> fin_cases i <;> fin_cases j <;>
      simp_all [countRegister, output, setup, work, others, PackingSetupMachine.output]

def endpointSlots (fixed : InventoryData) (K : Nat) (right : Bool) :
    (Fin 7 ⊕ Fin 6) ↪ Tape fixed K :=
  localSlots (slots fixed K) (endpointRegisters fixed K right)

theorem endpoint_outside (fixed : InventoryData) (K : Nat) (right : Bool)
    (tape : Extra) (i : Fin 7 ⊕ Fin 6) :
    endpointSlots fixed K right i ≠ Sum.inr tape := by
  simp [endpointSlots, localSlots, slots, registers]

def powerSlots (fixed : InventoryData) (K : Nat) (source : CountSource)
    (destination : Variable) : Fin 11 ↪ Tape fixed K where
  toFun := ![slots fixed K (.inl (countRegister fixed K source)),
    slots fixed K (.inl (item fixed K destination)),
    slots fixed K (.inl (work fixed K .temporary)),
    slots fixed K (.inr 0), slots fixed K (.inr 1), slots fixed K (.inr 2),
    slots fixed K (.inr 3), slots fixed K (.inr 4), slots fixed K (.inr 5),
    .inr .powerCounter, slots fixed K (.inl (work fixed K .reverse))]
  inj' := by
    intro i j h
    cases source with
    | input a =>
        fin_cases i <;> fin_cases j <;>
          simp_all [countRegister, input, setup, work, item, inputs, others,
            slots, registers, PackingSetupMachine.input]
        all_goals
          first
          | change (Sum.inl (Sum.inr _) : Register fixed K) = Sum.inl (Sum.inl _) at h
          | change (Sum.inl (Sum.inl _) : Register fixed K) = Sum.inl (Sum.inr _) at h
          simp at h
    | output a =>
        fin_cases i <;> fin_cases j <;>
          simp_all [countRegister, output, setup, work, item, inputs, others,
            slots, registers, PackingSetupMachine.output]
        all_goals
          first
          | change (Sum.inl (Sum.inr _) : Register fixed K) = Sum.inl (Sum.inl _) at h
          | change (Sum.inl (Sum.inl _) : Register fixed K) = Sum.inl (Sum.inr _) at h
          simp at h
    | endpoint right =>
        cases right <;> fin_cases i <;> fin_cases j <;>
          simp_all [countRegister, work, item, inputs, others, slots, registers]
        all_goals
          first
          | change (Sum.inl (Sum.inr _) : Register fixed K) = Sum.inl (Sum.inl _) at h
          | change (Sum.inl (Sum.inl _) : Register fixed K) = Sum.inl (Sum.inr _) at h
          simp at h

def decoderSlots (fixed : InventoryData) (K : Nat) (right : Bool) : Fin 3 ↪ Tape fixed K where
  toFun := ![.inr .endpoints, .inr .decodeScratch,
    slots fixed K (.inl (countRegister fixed K (.endpoint right)))]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [slots, registers]

def thresholdSlots (fixed : InventoryData) (K : Nat) : Fin 3 ↪ Tape fixed K where
  toFun := ![.inr .threshold, .inr .decodeScratch, slots fixed K (.inl (input fixed K .k))]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [slots, registers]

end BinPackingGap.GraphPackingRegisters

end

end OAI
