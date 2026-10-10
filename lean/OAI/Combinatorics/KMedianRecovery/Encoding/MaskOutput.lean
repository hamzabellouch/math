import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.FinSets

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMaskOutput
open WordOperations WordList
variable {n : ℕ}
noncomputable def member (x : List Bool) : List Bool :=
  [BinaryNatSet.contains (pairBits (discardPrefix x,extractPrefix x))]
noncomputable def member_computes : PolyComputes member :=
  (discardPrefix_computes.pair extractPrefix_computes).comp BinaryNatSet.contains_computes
lemma member_set (S : Finset (Fin n)) (i : Fin n) :
    member (pairBits (BinaryFinSet.encode S,i.val.bits))=[decide (i∈S)] := by
  simp only [member,extractPrefix_pairBits,discardPrefix_pairBits,BinaryFinSet.encode,
    BinaryNatSet.encode,BinaryNatSet.contains_pack,Finset.mem_sort,BinaryFinSet.values,
    Finset.mem_image,Fin.val_inj,exists_eq_right]
noncomputable def run (x : List Bool) : List Bool :=
  Flatten.run (mapWith member (pairBits (discardPrefix x,BinaryEllipsoidInitial.indices (extractPrefix x))))
noncomputable def run_computes : PolyComputes run := by
  unfold run
  have computes := (discardPrefix_computes.pair (extractPrefix_computes.comp BinaryEllipsoidInitial.indices_computes)).comp
    ((mapWith_computes member_computes).comp Flatten.run_computes)
  simpa only [Function.comp_def] using computes
lemma run_set (S : Finset (Fin n)) :
    run (pairBits (List.replicate n true,BinaryFinSet.encode S))=BinaryInputParser.Metric.mask S := by
  rw [run,extractPrefix_pairBits,discardPrefix_pairBits,BinaryEllipsoidInitial.indices_replicate,mapWith_ofFn]
  simp only [member_set,Flatten.run_encode]
  change (List.ofFn (fun i:Fin n=>[decide (i∈S)])).flatten=List.ofFn (fun i:Fin n=>decide (i∈S))
  rw [show List.ofFn (fun i:Fin n=>[decide (i∈S)])=(List.ofFn (fun i:Fin n=>decide (i∈S))).map (fun b=>[b]) from (List.map_ofFn (f:=fun i:Fin n=>decide (i∈S)) (g:=fun b:Bool=>[b])).symm]
  exact List.flatMap_singleton' _
end MetricKMedianRecovery.BitMachine.BinaryMaskOutput

end OAI
