import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.FinSets

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
variable {n : ℕ}
noncomputable def decode (n : ℕ) (x : List Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i=>BinaryNatSet.contains (pairBits (i.val.bits,x)))
lemma decode_encode (S : Finset (Fin n)) : decode n (encode S)=S := by
  classical
  ext i
  simp only [decode,encode,BinaryNatSet.encode,BinaryNatSet.contains_pack,Finset.mem_filter,
    Finset.mem_univ,true_and,decide_eq_true_eq,Finset.mem_sort,values,Finset.mem_image]
  exact ⟨fun ⟨j,hj,he⟩=>Fin.val_injective he ▸ hj,fun hi=>⟨i,hi,rfl⟩⟩
noncomputable def memberOp (x : List Bool) : List Bool :=
  [BinaryNatSet.contains (pairBits (discardPrefix x,extractPrefix x))]
noncomputable def memberOp_computes : PolyComputes memberOp :=
  (discardPrefix_computes.pair extractPrefix_computes).comp BinaryNatSet.contains_computes
noncomputable def mask (x : List Bool) : List Bool :=
  Flatten.run (mapWith memberOp (pairBits (discardPrefix x,BinaryEllipsoidInitial.indices (extractPrefix x))))
noncomputable def mask_computes : PolyComputes mask := by
  have computation := (discardPrefix_computes.pair (extractPrefix_computes.comp BinaryEllipsoidInitial.indices_computes)).comp
    ((mapWith_computes memberOp_computes).comp Flatten.run_computes)
  unfold mask
  simpa only [Function.comp_def] using computation
lemma mask_pack (S : Finset (Fin n)) :
    mask (pairBits (List.replicate n true,encode S))=List.ofFn (fun i:Fin n=>decide (i∈S)) := by
  classical
  rw [mask,extractPrefix_pairBits,discardPrefix_pairBits,BinaryEllipsoidInitial.indices_replicate,mapWith_ofFn,Flatten.run_encode]
  simp only [memberOp,discardPrefix_pairBits,extractPrefix_pairBits,encode,BinaryNatSet.encode,
    BinaryNatSet.contains_pack,Finset.mem_sort]
  have hfun : (fun i:Fin n=>[decide (i.val∈values S)])=(fun i:Fin n=>[decide (i∈S)]) := by
    funext i
    congr 1
    apply decide_eq_decide.mpr
    simp only [values,Finset.mem_image]
    exact ⟨fun ⟨j,hj,he⟩=>Fin.val_injective he ▸ hj,fun hi=>⟨i,hi,rfl⟩⟩
  rw [hfun]
  simp only [List.ofFn_eq_map,← List.flatMap_def,← List.map_eq_flatMap]
end MetricKMedianRecovery.BitMachine.BinaryFinSet

end OAI
