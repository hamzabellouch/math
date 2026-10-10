import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.ColorLabelMachine

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingReference
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryRationalSort (entryBits)
attribute [local irreducible] WordList.mapWith
variable {n l : ℕ}
def leafBits (v : Fin n) (r : ℚ) : List Bool := pairBits (v.val.bits,BinaryRational.encode r)
def pack (Δ : ℚ) (A : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) (row : Fin n→ℚ) : List Bool :=
  encode [n.bits,BinaryRational.encode Δ,BinaryFinSet.encode A,
    encode (List.ofFn (fun j=>leafBits (v j) (r j))),RationalMatrix.rowEncode row]
noncomputable def original (x : List Bool) : List Bool :=
  pairBits (Lookup.run (pairBits (discardPrefix x,extractPrefix x)),discardPrefix x)
noncomputable def original_computes : PolyComputes original :=
  ((discardPrefix_computes.pair extractPrefix_computes).comp Lookup.run_computes).pair discardPrefix_computes
lemma original_pack (row : Fin n→ℚ) (v : Fin n) :
    original (pairBits (RationalMatrix.rowEncode row,v.val.bits))=entryBits (toLex (row v,v.val)) := by
  simp only [original,extractPrefix_pairBits,discardPrefix_pairBits,RationalMatrix.rowEncode_eq,lookup_ofFn,entryBits,ofLex_toLex]
noncomputable def originals (x : List Bool) : List Bool := mapWith original (pairBits (field 4 x,field 2 x))
noncomputable def originals_computes : PolyComputes originals :=
  ((field_computes 4).pair (field_computes 2)).comp (mapWith_computes original_computes)
lemma originals_pack (Δ : ℚ) (A : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) (row : Fin n→ℚ) :
    originals (pack Δ A v r row)=encode ((A.sort (·≤·)).map (fun i=>entryBits (toLex (row i,i.val)))) := by
  simp only [originals,pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    BinaryFinSet.encode_eq,mapWith_encode,List.map_map,Function.comp_def,original_pack]
noncomputable def leaf (x : List Bool) : List Bool :=
  pairBits (BinaryRational.encode
    (BinaryRational.decode (Lookup.run (pairBits (extractPrefix (discardPrefix (discardPrefix x)),discardPrefix (extractPrefix x))))+
      BinaryRational.decode (discardPrefix (discardPrefix (discardPrefix x)))),
    (value (extractPrefix (extractPrefix x))+value (extractPrefix (discardPrefix x))+1).bits)
noncomputable def leaf_computes : PolyComputes leaf := by
  have hn : PolyComputes (fun x=>(value (extractPrefix (extractPrefix x))+value (extractPrefix (discardPrefix x))+1).bits) := by
    simpa only [Function.comp_def,value_bits] using
      (NatOps.add (NatOps.add (extractPrefix_computes.comp extractPrefix_computes)
        (discardPrefix_computes.comp extractPrefix_computes)) (const_computes (1:ℕ).bits))
  exact (RatOps.add (RatOps.ofWords (((discardPrefix_computes.comp discardPrefix_computes).comp extractPrefix_computes).pair
      (extractPrefix_computes.comp discardPrefix_computes) |>.comp Lookup.run_computes))
    (RatOps.ofWords ((discardPrefix_computes.comp discardPrefix_computes).comp discardPrefix_computes))).pair hn
lemma leaf_pack (row : Fin n→ℚ) (j : ℕ) (v : Fin n) (r : ℚ) :
    leaf (pairBits (pairBits (n.bits,RationalMatrix.rowEncode row),pairBits (j.bits,leafBits v r)))=
      entryBits (toLex (row v+r,n+j+1)) := by
  simp only [leaf,leafBits,extractPrefix_pairBits,discardPrefix_pairBits,RationalMatrix.rowEncode_eq,
    lookup_ofFn,BinaryRational.decode_encode,value_bits,entryBits,ofLex_toLex]
noncomputable def leaves (x : List Bool) : List Bool := mapWith leaf
  (pairBits (pairBits (field 0 x,field 4 x),Zip.run (pairBits (Indices.run (field 3 x),field 3 x))))
noncomputable def leaves_computes : PolyComputes leaves :=
  (((field_computes 0).pair (field_computes 4)).pair
    ((((field_computes 3).comp Indices.run_computes).pair (field_computes 3)).comp Zip.run_computes)).comp (mapWith_computes leaf_computes)
lemma leaves_pack (Δ : ℚ) (A : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) (row : Fin n→ℚ) :
    leaves (pack Δ A v r row)=encode (List.ofFn (fun j=>entryBits (toLex (row (v j)+r j,n+j.val+1)))) := by
  simp only [leaves,pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    indices_ofFn,Zip.run_encode,zip_ofFn,List.map_ofFn,Function.comp_def,mapWith_ofFn,leaf_pack]
def values (Δ : ℚ) (A : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) (row : Fin n→ℚ) : List (ℚ ×ₗ ℕ) :=
  (A.sort (·≤·)).map (fun i=>toLex (row i,i.val))++
    toLex (Δ,n)::List.ofFn (fun j=>toLex (row (v j)+r j,n+j.val+1))
noncomputable def entries (x : List Bool) : List Bool := originals x++cons (pairBits (field 1 x,field 0 x)) (leaves x)
noncomputable def entries_computes : PolyComputes entries :=
  originals_computes.append (cons_computes ((field_computes 1).pair (field_computes 0)) leaves_computes)
lemma entries_pack (Δ : ℚ) (A : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) (row : Fin n→ℚ) :
    entries (pack Δ A v r row)=encode ((values Δ A v r row).map entryBits) := by
  rw [entries,originals_pack,leaves_pack]
  simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  simp only [values,List.map_append,List.map_cons,List.map_map,Function.comp_def,List.map_ofFn,entryBits,ofLex_toLex,
    encode_append,encode]
lemma values_nonempty (Δ : ℚ) (A : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) (row : Fin n→ℚ) :
    (values Δ A v r row).toFinset.Nonempty := by
  refine ⟨toLex (Δ,n),?_⟩
  simp only [List.mem_toFinset,values,List.mem_append,List.mem_cons,List.mem_ofFn]
  exact Or.inr (Or.inl trivial)
noncomputable def run (x : List Bool) : List Bool := BinaryRationalMinKey.run (entries x)
noncomputable def run_computes : PolyComputes run := entries_computes.comp BinaryRationalMinKey.run_computes
lemma run_pack (Δ : ℚ) (A : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) (row : Fin n→ℚ) :
    run (pack Δ A v r row)=entryBits ((values Δ A v r row).toFinset.min' (values_nonempty Δ A v r row)) := by
  rw [run,entries_pack,BinaryRationalMinKey.run_pack]
end MetricKMedianRecovery.BitMachine.BinarySamplingReference

end OAI
