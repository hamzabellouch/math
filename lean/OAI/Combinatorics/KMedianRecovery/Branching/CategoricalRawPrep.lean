import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.CompletionFillMath
import OAI.Combinatorics.KMedianRecovery.Branching.CategoricalOutput

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Categorical.Explicit
variable {q a : ℕ}
noncomputable def pack (ctx : List Bool) (part : Fin q→Fin a)
    (bits : Categorical.BinaryOracleIndex (Fin q) a (exponent a) (samples q a)→Bool) : List Bool :=
  pairBits (encode [ctx,partBits part,List.replicate a true],Tape.raw q a (exponent a) (samples q a) bits)
noncomputable def qword (x : List Bool) : List Bool := Count.run (field 1 (extractPrefix x))
noncomputable def aword (x : List Bool) : List Bool := field 2 (extractPrefix x)
noncomputable def dimensions (x : List Bool) : List Bool := pairBits (qword x,aword x)
noncomputable def qword_computes : PolyComputes qword := (extractPrefix_computes.comp (field_computes 1)).comp Count.run_computes
noncomputable def aword_computes : PolyComputes aword := extractPrefix_computes.comp (field_computes 2)
noncomputable def dimensions_computes : PolyComputes dimensions := qword_computes.pair aword_computes
noncomputable def tword (x : List Bool) : List Bool := Resources.tword (dimensions x)
noncomputable def lword (x : List Bool) : List Bool := Resources.lword (dimensions x)
noncomputable def bword (x : List Bool) : List Bool := Resources.bword (dimensions x)
attribute [local irreducible] Resources.tword Resources.lword Resources.bword dimensions
noncomputable def tword_computes : PolyComputes tword := dimensions_computes.comp Resources.tword_computes
noncomputable def lword_computes : PolyComputes lword := dimensions_computes.comp Resources.lword_computes
noncomputable def bword_computes : PolyComputes bword := dimensions_computes.comp Resources.bword_computes
noncomputable def leftShape (x : List Bool) : List Bool := encode [tword x,qword x,lword x,aword x,bword x]
noncomputable def rightShape (x : List Bool) : List Bool := encode [aword x,bword x]
noncomputable def leftShape_computes : PolyComputes leftShape := cons_computes tword_computes
  (cons_computes qword_computes (cons_computes lword_computes (cons_computes aword_computes (cons_computes bword_computes (const_computes [])))))
noncomputable def rightShape_computes : PolyComputes rightShape := cons_computes aword_computes (cons_computes bword_computes (const_computes []))
noncomputable def cut (x : List Bool) : List Bool := BinarySeed.product 5 (leftShape x)
attribute [local irreducible] BinarySeed.product leftShape
noncomputable def cut_computes : PolyComputes cut := leftShape_computes.comp (BinarySeed.product_computes 5)
noncomputable def left (x : List Bool) : List Bool := BinarySeed.nest 4 (pairBits (leftShape x,RawTake.run (pairBits (cut x,discardPrefix x))))
noncomputable def right (x : List Bool) : List Bool := BinarySeed.nest 1 (pairBits (rightShape x,RawDrop.run (pairBits (cut x,discardPrefix x))))
attribute [local irreducible] BinarySeed.nest RawTake.run RawDrop.run cut rightShape tword lword bword
noncomputable def left_computes : PolyComputes left :=
  (leftShape_computes.pair ((cut_computes.pair discardPrefix_computes).comp RawTake.run_computes)).comp (BinarySeed.nest_computes 4)
noncomputable def right_computes : PolyComputes right :=
  (rightShape_computes.pair ((cut_computes.pair discardPrefix_computes).comp RawDrop.run_computes)).comp (BinarySeed.nest_computes 1)
noncomputable def runInput (x : List Bool) : List Bool := encode [field 0 (extractPrefix x),field 1 (extractPrefix x),aword x,tword x,left x]
noncomputable def runInput_computes : PolyComputes runInput := cons_computes (extractPrefix_computes.comp (field_computes 0))
  (cons_computes (extractPrefix_computes.comp (field_computes 1)) (cons_computes aword_computes (cons_computes tword_computes (cons_computes left_computes (const_computes [])))))
noncomputable def run (x : List Bool) : List Bool := pairBits (runInput x,right x)
noncomputable def run_computes : PolyComputes run := runInput_computes.pair right_computes
section Correct
variable (ctx : List Bool) (part : Fin q→Fin a)
  (bits : Categorical.BinaryOracleIndex (Fin q) a (exponent a) (samples q a)→Bool)
local notation "xx" => pack ctx part bits
lemma qword_pack : qword xx=List.replicate q true := by
  simp only [qword,pack,extractPrefix_pairBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,partBits,Count.run_encode,List.length_ofFn]
lemma aword_pack : aword xx=List.replicate a true := by
  simp only [aword,pack,extractPrefix_pairBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma dimensions_pack : dimensions xx=Resources.pack q a := by rw [dimensions,qword_pack,aword_pack]; rfl
lemma tword_pack : tword xx=List.replicate (steps a) true := by rw [tword,dimensions_pack,Resources.tword_pack]
lemma leftShape_pack : leftShape xx=BinarySeed.shape [steps a,q,samples q a,a,exponent a] := by
  rw [leftShape,tword_pack,qword_pack,lword,dimensions_pack,Resources.lword_pack,aword_pack,bword,dimensions_pack,Resources.bword_pack]; rfl
lemma rightShape_pack : rightShape xx=BinarySeed.shape [a,exponent a] := by
  rw [rightShape,aword_pack,bword,dimensions_pack,Resources.bword_pack]; rfl
lemma cut_pack : cut xx=(Tape.M q a (exponent a) (samples q a)).bits := by
  rw [cut,leftShape_pack]
  change BinarySeed.product [steps a,q,samples q a,a,exponent a].length (BinarySeed.shape _) = _
  rw [BinarySeed.product_shape]
  congr 1
  simp only [Tape.M,BinarySeed.count,steps,List.prod_cons,List.prod_nil,Nat.mul_one]
lemma left_pack : left xx=encode (List.ofFn (fun t=>oracleBits ((Categorical.binarySeedEquiv (Fin q) a (exponent a) (samples q a) bits).1 t))) := by
  rw [left,leftShape_pack,cut_pack]
  simp only [pack,discardPrefix_pairBits,RawTake.run_pack,Tape.raw,←Tape.raw_left_length q a (exponent a) (samples q a) bits,List.take_left]
  change BinarySeed.nest [steps a,q,samples q a,a].length (pairBits (BinarySeed.shape ([steps a,q,samples q a,a]++[exponent a]),_)) = _
  have he := BinarySeed.nest_tensor (ds := [2^(exponent a),q,samples q a,a]) (b := exponent a)
    ((Tape.tensors q a (exponent a) (samples q a)) bits).1
  rw [show steps a=2^(exponent a) from rfl]
  rw [he,Tape.parsed_left]
lemma right_pack : right xx=seedBits ((Categorical.binarySeedEquiv (Fin q) a (exponent a) (samples q a) bits).2) := by
  rw [right,rightShape_pack,cut_pack]
  simp only [pack,discardPrefix_pairBits,RawDrop.run_encode,Tape.raw,←Tape.raw_left_length q a (exponent a) (samples q a) bits,List.drop_left]
  change BinarySeed.nest [a].length (pairBits (BinarySeed.shape ([a]++[exponent a]),_)) = _
  rw [BinarySeed.nest_tensor,Tape.parsed_right]
lemma run_pack : run xx=outputPack ctx part (Categorical.binarySeedEquiv (Fin q) a (exponent a) (samples q a) bits) := by
  rw [run,runInput,aword_pack,tword_pack,left_pack,right_pack]
  simp only [pack,extractPrefix_pairBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,outputPack,runPack,List.map_ofFn,Function.comp_def,steps]
end Correct
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFill
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a : ℕ}
def elemBits (e : Fin q) := e.val.bits
def pack (part : Fin q→Fin a) (o : Fin a→Fin q) (xs : List (Fin q)) :=
  encode [encode (List.ofFn (fun e=>(part e).val.bits)),encode (List.ofFn (fun j=>(o j).val.bits)),encode (xs.map elemBits)]
noncomputable def test (x : List Bool) : Bool :=
  decide (value (Lookup.run (pairBits (discardPrefix x,field 0 (extractPrefix x))))=value (field 1 (extractPrefix x)))
noncomputable def test_computes : PolyComputes (fun x=>[test x]) :=
  NatOps.eq (((discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 0))).comp Lookup.run_computes))
    (extractPrefix_computes.comp (field_computes 1))
noncomputable def options (x : List Bool) : List Bool :=
  filterWith test (pairBits (encode [field 0 (extractPrefix x),discardPrefix x],field 2 (extractPrefix x)))
noncomputable def options_computes : PolyComputes options :=
  ((cons_computes (extractPrefix_computes.comp (field_computes 0)) (cons_computes discardPrefix_computes (const_computes []))).pair
    (extractPrefix_computes.comp (field_computes 2))).comp (filterWith_computes test_computes)
noncomputable def pick (x : List Bool) : List Bool :=
  if options x=[] then Lookup.run (pairBits (discardPrefix x,field 1 (extractPrefix x))) else WordList.head (options x)
attribute [local irreducible] options
noncomputable def pick_computes : PolyComputes pick := by
  have h := (options_computes.comp isEmpty_computes).cond
    ((discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 1))).comp Lookup.run_computes)
    (options_computes.comp WordList.head_computes)
  unfold pick
  simpa only [decide_eq_true_eq,Function.comp_def] using h
lemma options_pack (part : Fin q→Fin a) (o : Fin a→Fin q) (xs : List (Fin q)) (j : Fin a) :
    options (pairBits (pack part o xs,j.val.bits))=encode ((xs.filter (fun e=>part e=j)).map elemBits) := by
  simp only [options,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    extractPrefix_pairBits,discardPrefix_pairBits,filterWith_encode,List.filter_map,Function.comp_def,
    test,elemBits,lookup_ofFn,value_bits,Fin.ext_iff]
lemma pick_pack (part : Fin q→Fin a) (o : Fin a→Fin q) (xs : List (Fin q)) (j : Fin a) :
    pick (pairBits (pack part o xs,j.val.bits))=elemBits (Completion.Canonical.pick part o xs j) := by
  rw [pick,options_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    extractPrefix_pairBits,discardPrefix_pairBits,lookup_ofFn,Completion.Canonical.pick]
  cases h : xs.filter (fun e=>part e=j) with
  | nil=>rfl
  | cons e es=>
    simp only [List.map_cons,encode]
    have hn : cons (elemBits e) (encode (es.map elemBits))≠[] := by
      unfold cons; exact List.cons_ne_nil _ _
    rw [ite_eq_right hn]
    simp only [head,cons,List.tail_cons,extractPrefix_pairBits,List.head?_cons,Option.getD_some]

noncomputable def run (x : List Bool) : List Bool := mapWith pick (pairBits (x,Indices.run (field 1 x)))
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def,id_eq] using
    (id_computes.pair ((field_computes 1).comp Indices.run_computes)).comp (mapWith_computes pick_computes)
lemma run_pack (part : Fin q→Fin a) (o : Fin a→Fin q) (xs : List (Fin q)) :
    run (pack part o xs)=encode (List.ofFn (fun j=>elemBits (Completion.Canonical.pick part o xs j))) := by
  rw [run]
  have hi : field 1 (pack part o xs)=encode (List.ofFn (fun j=>(o j).val.bits)) := by
    simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [hi,indices_ofFn,mapWith_ofFn]
  apply congrArg encode
  apply congrArg List.ofFn
  funext j
  exact pick_pack part o xs j
end MetricKMedianRecovery.BitMachine.BinaryCompletionFill

end OAI
