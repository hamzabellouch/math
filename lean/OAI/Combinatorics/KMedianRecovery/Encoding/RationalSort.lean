import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.WordTake

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordOperations WordList BinaryArithmetic

def entryBits (p : ℚ ×ₗ ℕ) : List Bool := pairBits (BinaryRational.encode (ofLex p).1,(ofLex p).2.bits)
def lt (x : List Bool) : Bool :=
  decide (BinaryRational.decode (extractPrefix (extractPrefix x))<BinaryRational.decode (extractPrefix (discardPrefix x))) ||
  (decide (BinaryRational.decode (extractPrefix (extractPrefix x))=BinaryRational.decode (extractPrefix (discardPrefix x))) &&
    decide (value (discardPrefix (extractPrefix x))<value (discardPrefix (discardPrefix x))))
noncomputable def lt_computes : PolyComputes (fun x=>[lt x]) :=
  (RatOps.lt (RatOps.ofWords (extractPrefix_computes.comp extractPrefix_computes))
    (RatOps.ofWords (discardPrefix_computes.comp extractPrefix_computes))).or
  ((RatOps.eq (RatOps.ofWords (extractPrefix_computes.comp extractPrefix_computes))
    (RatOps.ofWords (discardPrefix_computes.comp extractPrefix_computes))).and
  (NatOps.lt (extractPrefix_computes.comp discardPrefix_computes) (discardPrefix_computes.comp discardPrefix_computes)))
lemma lt_pack (a b : ℚ ×ₗ ℕ) : lt (pairBits (entryBits a,entryBits b))=decide (a<b) := by
  simp only [lt,entryBits,extractPrefix_pairBits,discardPrefix_pairBits,BinaryRational.decode_encode,
    value_bits,Prod.Lex.lt_iff,Bool.decide_or,Bool.decide_and]
noncomputable def sort : List Bool→List Bool := Sort.run lt
noncomputable def sort_computes : PolyComputes sort := Sort.run_computes lt_computes
lemma sort_pack (xs : List (ℚ ×ₗ ℕ)) :
    sort (encode (xs.map entryBits))=encode ((xs.toFinset.sort (·≤·)).map entryBits) :=
  Sort.run_encode entryBits lt lt_pack xs
noncomputable def ranked (x : List Bool) : List Bool :=
  mapWith (fun y=>pairBits (discardPrefix (discardPrefix y),extractPrefix (discardPrefix y)))
    (pairBits ([],Zip.run (pairBits (Indices.run x,x))))
noncomputable def ranked_computes : PolyComputes ranked := by
  have computation := ((const_computes []).pair ((Indices.run_computes.pair id_computes).comp Zip.run_computes)).comp
    (mapWith_computes ((discardPrefix_computes.comp discardPrefix_computes).pair (discardPrefix_computes.comp extractPrefix_computes)))
  unfold ranked
  simpa only [Function.comp_def, id_eq] using computation
def ranking {r : ℕ} (v : Fin r→ℚ) (i : Fin r) : ℚ ×ₗ ℕ := toLex (v i,i.val)
lemma ranked_pack {r : ℕ} (v : Fin r→ℚ) :
    ranked (encode (List.ofFn (fun i=>BinaryRational.encode (v i))))=encode (List.ofFn (fun i=>entryBits (ranking v i))) := by
  simp only [ranked,indices_ofFn,Zip.run_encode,zip_ofFn,List.map_ofFn,Function.comp_def,mapWith_ofFn,
    extractPrefix_pairBits,discardPrefix_pairBits,entryBits,ranking,ofLex_toLex]
attribute [local irreducible] sort ranked Take.run
noncomputable def bottom (x : List Bool) : List Bool :=
  Take.run (pairBits (extractPrefix x,sort (ranked (discardPrefix x))))
noncomputable def bottom_computes : PolyComputes bottom :=
  (extractPrefix_computes.pair ((discardPrefix_computes.comp ranked_computes).comp sort_computes)).comp Take.run_computes
lemma bottom_pack {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
    bottom (pairBits (k.bits,encode (List.ofFn (fun i=>BinaryRational.encode (v i)))) )=
      encode ((((Finset.univ.image (ranking v)).sort (·≤·)).take k).map entryBits) := by
  simp only [bottom,extractPrefix_pairBits,discardPrefix_pairBits,ranked_pack]
  rw [show List.ofFn (fun i=>entryBits (ranking v i))=(List.ofFn (ranking v)).map entryBits by rw [List.map_ofFn]; rfl]
  rw [sort_pack,Take.run_encode,←Fin.univ_image_def,←List.map_take]
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

namespace MetricKMedianRecovery.BitMachine.BinaryNatSet
open WordOperations WordList BinaryArithmetic
abbrev pack (xs : List ℕ) := WordList.encode (xs.map Nat.bits)
abbrev encode (S : Finset ℕ) := pack (S.sort (·≤·))
def lt (x : List Bool) : Bool := decide (value (extractPrefix x)<value (discardPrefix x))
noncomputable def lt_computes : PolyComputes (fun x=>[lt x]) := NatOps.lt extractPrefix_computes discardPrefix_computes
lemma lt_pack (a b : ℕ) : lt (pairBits (a.bits,b.bits))=decide (a<b) := by
  simp only [lt,extractPrefix_pairBits,discardPrefix_pairBits,value_bits]
noncomputable def sort : List Bool→List Bool := Sort.run lt
noncomputable def sort_computes : PolyComputes sort := Sort.run_computes lt_computes
lemma sort_pack (xs : List ℕ) : sort (pack xs)=encode xs.toFinset := Sort.run_encode _ _ lt_pack _
noncomputable def union (x : List Bool) : List Bool := sort (extractPrefix x++discardPrefix x)
noncomputable def union_computes : PolyComputes union := (extractPrefix_computes.append discardPrefix_computes).comp sort_computes
lemma union_pack (xs ys : List ℕ) : union (pairBits (pack xs,pack ys))=encode (xs.toFinset∪ys.toFinset) := by
  simp only [union,extractPrefix_pairBits,discardPrefix_pairBits,←WordList.encode_append,←List.map_append,
    sort_pack,List.toFinset_append]
noncomputable def contains : List Bool→Bool := BinaryPhaseFirst.contains
noncomputable def contains_computes : PolyComputes (fun x=>[contains x]) := BinaryPhaseFirst.contains_computes
lemma contains_pack (a : ℕ) (xs : List ℕ) : contains (pairBits (a.bits,pack xs))=decide (a∈xs) := by
  simp only [contains,BinaryPhaseFirst.contains,Find.run_encode]
  apply decide_eq_decide.mpr
  simp only [ne_eq,BinaryOpeningActivity.optionEncode_nil_iff,List.find?_eq_none,List.mem_map,
    forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,BinaryPhaseFirst.natEq,
    extractPrefix_pairBits,discardPrefix_pairBits,value_bits,decide_eq_true_eq,not_forall,exists_prop,not_not]
  exact ⟨fun ⟨b,hb,he⟩=>he ▸ hb,fun ha=>⟨a,ha,rfl⟩⟩
noncomputable def absent (x : List Bool) : Bool := !contains (pairBits (discardPrefix x,extractPrefix x))
noncomputable def absent_computes : PolyComputes (fun x=>[absent x]) :=
  ((discardPrefix_computes.pair extractPrefix_computes).comp contains_computes).not
noncomputable def diff (x : List Bool) : List Bool := sort (filterWith absent (pairBits (discardPrefix x,extractPrefix x)))
noncomputable def diff_computes : PolyComputes diff :=
  ((discardPrefix_computes.pair extractPrefix_computes).comp (filterWith_computes absent_computes)).comp sort_computes
lemma diff_pack (xs ys : List ℕ) : diff (pairBits (pack xs,pack ys))=encode (xs.toFinset\ys.toFinset) := by
  simp only [diff,extractPrefix_pairBits,discardPrefix_pairBits,filterWith_encode,pack,List.filter_map,
    Function.comp_def,absent,contains_pack,←decide_not]
  rw [sort_pack]
  congr 1
  ext a
  simp
lemma union_encode (S T : Finset ℕ) : union (pairBits (encode S,encode T))=encode (S∪T) := by
  simpa only [Finset.sort_toFinset] using union_pack (S.sort (·≤·)) (T.sort (·≤·))
lemma diff_encode (S T : Finset ℕ) : diff (pairBits (encode S,encode T))=encode (S\T) := by
  simpa only [Finset.sort_toFinset] using diff_pack (S.sort (·≤·)) (T.sort (·≤·))
end MetricKMedianRecovery.BitMachine.BinaryNatSet

end OAI
