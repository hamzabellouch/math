import OAI.Computability.BinPacking.Arithmetic.GraphTallyMachine

namespace OAI

namespace BinPackingGap.DropPackingBoundMachine

open Turing BinPackingGames.Foundations.Complexity BinPackingGames.Reduction
open BinaryEncoding

inductive Mode
  | name | digit | copy
  deriving DecidableEq

protected abbrev Mode.enumList : List Mode := [.name, .digit, .copy]

protected theorem Mode.enumList_getElem?_ctorIdx_eq (x : Mode) :
    Mode.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Mode.enumList_nodup : Mode.enumList.Nodup := by decide

instance : Fintype Mode where
  elems := ⟨Mode.enumList, Mode.enumList_nodup⟩
  complete x := by cases x <;> decide

def transition : Mode → Bool → Mode
  | .name, true => .digit
  | .name, false => .copy
  | .digit, _ => .name
  | .copy, _ => .copy

def emit : Mode → Bool → List Bool
  | .copy, bit => [bit]
  | _, _ => []

def output : Mode → List Bool → List Bool := MachineTransducer.output transition emit

theorem output_copy (input : List Bool) : output .copy input = input := by
  induction input with
  | nil => rfl
  | cons bit tail ih =>
    simpa only [output, MachineTransducer.output, transition, emit, List.singleton_append] using
      congrArg (bit :: ·) ih

theorem output_frame (bits suffix : List Bool) :
    output .name (BinPackingCompleteness.BinaryEncoding.frame bits ++ suffix) = suffix := by
  induction bits with
  | nil => simpa [BinPackingCompleteness.BinaryEncoding.frame, output,
      MachineTransducer.output, transition, emit] using output_copy suffix
  | cons bit bits ih =>
    simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append,
      output, MachineTransducer.output, transition, emit, List.nil_append] using ih

theorem output_encoded (out : RawReductionOutput) :
    output .name (rawReductionOutputBits out) = rawInstanceBits out.2 :=
  output_frame out.1.bits (rawInstanceBits out.2)

def reversedMachine : FinTM2 := MachineTransducer.machine Mode.name transition emit

def reversedRun (out : RawReductionOutput) :
    TM2OutputsInTime reversedMachine (rawReductionOutputBits out)
      (some (rawInstanceBits out.2).reverse) (2 * (rawReductionOutputBits out).length + 1) where
  steps := 2 * (rawReductionOutputBits out).length + 1
  evals_in_steps := by
    have run := MachineTransducer.transduce_init_steps Mode.name transition emit
      (rawReductionOutputBits out)
    change (MachineTransducer.next Mode.name transition emit)^[2 * (rawReductionOutputBits out).length + 1]
      (some (initList reversedMachine (rawReductionOutputBits out))) =
      some (haltList reversedMachine (rawInstanceBits out.2).reverse)
    change (MachineTransducer.next Mode.name transition emit)^[2 * (rawReductionOutputBits out).length + 1]
      (some (initList reversedMachine (rawReductionOutputBits out))) =
      some (haltList reversedMachine (output .name (rawReductionOutputBits out)).reverse) at run
    rw [output_encoded] at run
    exact run
  steps_le_m := Nat.le_refl _

def machine : FinTM2 :=
  MachineSequential.machine reversedMachine MachineReverse.machine id false

def run (out : RawReductionOutput) :
    TM2OutputsInTime machine (rawReductionOutputBits out) (some (rawInstanceBits out.2))
      (5 * (rawReductionOutputBits out).length + 4) := by
  have second : TM2OutputsInTime MachineReverse.machine
      ((rawInstanceBits out.2).reverse.map id) (some (rawInstanceBits out.2))
      ((rawInstanceBits out.2).length + 1) := by
    simpa only [List.map_id, List.map_id_fun, List.reverse_reverse, List.length_reverse] using!
      MachineReverse.outputsInTime (rawInstanceBits out.2).reverse
  have full := MachineSequential.execute reversedMachine MachineReverse.machine id false
    (rawReductionOutputBits out) (rawInstanceBits out.2).reverse (rawInstanceBits out.2)
    (2 * (rawReductionOutputBits out).length + 1) ((rawInstanceBits out.2).length + 1)
    (reversedRun out) second
  refine { toEvalsTo := full.toEvalsTo, steps_le_m := ?_ }
  have h := full.steps_le_m
  have hlen : (rawInstanceBits out.2).length ≤ (rawReductionOutputBits out).length := by
    simp only [rawReductionOutputBits, List.length_append]
    omega
  change full.steps ≤ 2 * (rawReductionOutputBits out).length + 1 +
    2 * ((rawInstanceBits out.2).reverse.length + 1) + ((rawInstanceBits out.2).length + 1) at h
  rw [List.length_reverse] at h
  omega

noncomputable def computation :
    TM2ComputableInPolyTime rawReductionOutputBits rawInstanceBits
      (fun out : RawReductionOutput => out.2) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 5 * Polynomial.X + Polynomial.C 4
  outputsFun out := by
    change TM2OutputsInTime machine ((rawReductionOutputBits out).map id)
      (some ((rawInstanceBits out.2).map id)) _
    simpa only [List.map_id, List.map_id_fun, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using! run out

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm := by
  intro k
  rcases k with k | k | k <;> change Finite Bool <;> infer_instance

end BinPackingGap.DropPackingBoundMachine

end OAI
