import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.RealizedKernel

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryActions
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open RationalSampling
variable {n : ℕ}
attribute [local irreducible] RawTake.run
noncomputable def entry (k : ℕ) (x : List Bool) : List Bool :=
  pairBits (k.bits,RawTake.run (pairBits (discardPrefix x,extractPrefix x)))
noncomputable def entry_computes (k : ℕ) : PolyComputes (entry k) :=
  (const_computes k.bits).pair ((discardPrefix_computes.pair extractPrefix_computes).comp RawTake.run_computes)
noncomputable def block (k : ℕ) (x : List Bool) : List Bool :=
  mapWith (entry k) (pairBits (x,BinaryEllipsoidInitial.indices x))
noncomputable def block_computes (k : ℕ) : PolyComputes (block k) := by
  have computation := (id_computes.pair BinaryEllipsoidInitial.indices_computes).comp (mapWith_computes (entry_computes k))
  unfold block
  simpa only [Function.comp_def, id_eq] using computation
lemma block_replicate (k m : ℕ) : block k (List.replicate m true)=
    encode (List.ofFn (fun i : Fin m=>BinaryMenu.code k i.val)) := by
  simp only [block,BinaryEllipsoidInitial.indices_replicate,mapWith_encode,List.map_ofFn,Function.comp_def,
    entry,extractPrefix_pairBits,discardPrefix_pairBits,RawTake.run_pack,List.take_replicate]
  congr 2
  funext i
  rw [min_eq_left (Nat.le_of_lt i.isLt)]
  rfl
noncomputable def menus (x : List Bool) : List Bool :=
  block 0 (field 0 x)++block 1 (field 1 x++[true])++block 2 (field 2 x)
noncomputable def menus_computes : PolyComputes menus := by
  have computation := (((field_computes 0).comp (block_computes 0)).append (((field_computes 1).append (const_computes [true])).comp (block_computes 1))).append
    ((field_computes 2).comp (block_computes 2))
  unfold menus
  simpa only [Function.comp_def] using computation
lemma menus_weights (M E J : ℕ) : menus (BinaryMenu.weights M E J)=encode ((entries M E J).map (entryCode M E J)) := by
  simp only [menus,BinaryMenu.weights,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    ←List.replicate_succ',block_replicate,←encode_append,entries,List.map_append,List.map_ofFn,Function.comp_def,entryCode]
noncomputable def delete (x : List Bool) : List Bool := encode [(1:ℕ).bits,discardPrefix x,[]]
noncomputable def delete_computes : PolyComputes delete := cons_computes (const_computes _) (cons_computes discardPrefix_computes (const_computes (encode [[]])))
noncomputable def add (x : List Bool) : List Bool := encode [(2:ℕ).bits,extractPrefix x,discardPrefix x]
noncomputable def add_computes : PolyComputes add := cons_computes (const_computes _) (cons_computes extractPrefix_computes (cons_computes discardPrefix_computes (const_computes [])))
noncomputable def run (x : List Bool) : List Bool := encode [encode [(0:ℕ).bits,[],[]]]++
  mapWith delete (pairBits ([],extractPrefix x))++crossWith add (pairBits (extractPrefix x,menus (discardPrefix x)))
noncomputable def run_computes : PolyComputes run := by
  have computation := ((const_computes (encode [encode [(0:ℕ).bits,[],[]]])).append (((const_computes []).pair extractPrefix_computes).comp (mapWith_computes delete_computes))).append
    ((extractPrefix_computes.pair (discardPrefix_computes.comp menus_computes)).comp (crossWith_computes add_computes))
  unfold run
  simpa only [Function.comp_def] using computation
lemma clients_sort (D : Finset (Fin n)) : (clients D).map Subtype.val=D.sort (·≤·) := by
  have hh:=Finset.map_sort (Function.Embedding.subtype (·∈D)) D.attach (·≤·) (·≤·) (fun a _ b _=>Iff.rfl)
  simpa only [clients,Finset.attach_map_val,Function.Embedding.coe_subtype] using hh
lemma clients_bits (D : Finset (Fin n)) : BinaryFinSet.encode D=encode ((clients D).map (fun w=>w.val.val.bits)) := by
  rw [BinaryFinSet.encode_eq,←clients_sort D,List.map_map]; rfl
lemma run_pair (D : Finset (Fin n)) (M E J : ℕ) :
    run (pairBits (BinaryFinSet.encode D,BinaryMenu.weights M E J))=encode ((actions D M E J).map (actionCode D M E J)) := by
  simp only [run,extractPrefix_pairBits,discardPrefix_pairBits,clients_bits,menus_weights,mapWith_encode,crossWith_encode,
    actions,List.map_cons,List.map_append,List.product,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def,
    delete,add,extractPrefix_pairBits,discardPrefix_pairBits,actionCode,←encode_append,List.cons_append]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryActions

end OAI
