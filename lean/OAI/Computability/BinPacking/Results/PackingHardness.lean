import OAI.Computability.BinPacking.Hardness.LiteralSlotGraphComputation
import OAI.Computability.BinPacking.Hardness.PCPPackingGap
import OAI.Computability.BinPacking.Machines.GraphPackingMachine

namespace OAI

noncomputable section

namespace BinPackingGap

open Turing BinPackingGames.Foundations.Complexity BinPackingCompleteness

theorem packingGapNPHard (c : Nat) : PackingGapNPHard c := by
  intro L hL
  obtain ⟨source, runtime, hfinite, hsource⟩ := PCPFoundation.normalizedSource L hL
  let normalized : List Bool → LiteralSlotGraphMachine.NonemptyFormula := fun input =>
    ⟨PCPSourceHardness.formula source input, (hsource input).2.1⟩
  let first : TM2ComputableInPolyTime (id : List Bool → List Bool)
      LiteralSlotGraphMachine.inputBits normalized := {
    tm := runtime.tm
    inputAlphabet := runtime.inputAlphabet
    outputAlphabet := runtime.outputAlphabet
    time := runtime.time
    outputsFun input := runtime.outputsFun input }
  let graphRun := MachineSequential.composeBits first LiteralSlotGraphMachine.computation
  let packingRun := MachineSequential.composeBits graphRun
    (graphPackingComputation c PCPFoundation.rho)
  refine ⟨{
    reduce := fun input => PCPFoundation.packingOutput c (source.reduce input)
    computation := packingRun
    finiteAlphabet := ?_
    valid := fun input => PCPFoundation.packingOutput_valid c (source.reduce input)
    itemCount := fun input => PCPFoundation.packingOutput_count c (source.reduce input)
    itemLower := fun input i => PCPFoundation.packingOutput_size_lower c (source.reduce input) i
    completeness := ?_
    soundness := ?_ }⟩
  · exact MachineFiniteAlphabet.composeBits graphRun
      (graphPackingComputation c PCPFoundation.rho)
      (MachineFiniteAlphabet.composeBits first LiteralSlotGraphMachine.computation
        hfinite LiteralSlotGraphMachine.computation_finiteAlphabet)
      (graphPackingComputation_finiteAlphabet c PCPFoundation.rho)
  · intro input accepted
    exact PCPFoundation.packingOutput_complete c (source.reduce input)
      ((source.correct input).mp accepted)
  · intro input rejected
    exact PCPFoundation.packingOutput_sound c (source.reduce input)
      (fun satisfiable => rejected ((source.correct input).mpr satisfiable))

theorem packingPromiseNPHard (c : Nat) :
    PromiseNPHard BinaryEncoding.rawReductionOutputBits (packingPromise c) :=
  (packingGapNPHard c).promiseNPHard

end BinPackingGap

end

end OAI
