import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Op2
import OAI.Combinatorics.KMedianRecovery.Branching.BlueDPValue

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueMerge
open WordOperations WordList
variable {A : Type*}
def listEnc (enc : A→List Bool) (xs : List A) : List Bool := WordList.encode (xs.map enc)
lemma listEnc_append (enc : A→List Bool) (xs ys : List A) : listEnc enc (xs++ys)=listEnc enc xs++listEnc enc ys := by
  simp only [listEnc,List.map_append,WordList.encode_append]
noncomputable def payload (x : List Bool) : List Bool := discardPrefix (head x)
noncomputable def payload_computes : PolyComputes payload := WordList.head_computes.comp discardPrefix_computes
noncomputable def sum (x : List Bool) : List Bool := BinaryRational.encode
  (BinaryRational.decode (BinaryBlueChoice.score (extractPrefix x))+
    BinaryRational.decode (BinaryBlueChoice.score (discardPrefix x)))
noncomputable def sum_computes : PolyComputes sum :=
  RatOps.add (RatOps.ofWords (extractPrefix_computes.comp BinaryBlueChoice.score_computes))
    (RatOps.ofWords (discardPrefix_computes.comp BinaryBlueChoice.score_computes))
noncomputable def output (x : List Bool) : List Bool := WordList.encode
  [pairBits (sum x,payload (extractPrefix x)++payload (discardPrefix x))]
noncomputable def output_computes : PolyComputes output :=
  cons_computes (sum_computes.pair ((extractPrefix_computes.comp payload_computes).append
    (discardPrefix_computes.comp payload_computes))) (const_computes [])
noncomputable def run (x : List Bool) : List Bool :=
  if extractPrefix x=[] then [] else if discardPrefix x=[] then [] else output x
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def,decide_eq_true_eq] using
    (extractPrefix_computes.comp isEmpty_computes).cond (const_computes [])
      ((discardPrefix_computes.comp isEmpty_computes).cond (const_computes []) output_computes)
lemma run_pack (enc : A→List Bool) (x y : BlueDP.Candidate (List A)) :
    run (pairBits (BinaryBlueChoice.encode (listEnc enc) x,BinaryBlueChoice.encode (listEnc enc) y))=
      BinaryBlueChoice.encode (listEnc enc) (BlueDP.merge x y) := by
  cases x with
  | none=>simp [run,BinaryBlueChoice.encode,BlueDP.merge]
  | some x=>
    cases x with
    | mk q xs=>
      cases y with
      | none=>simp [run,BinaryBlueChoice.encode,BlueDP.merge]
      | some y=>
        cases y with
        | mk r ys=>
          simp only [run,extractPrefix_pairBits,discardPrefix_pairBits]
          have hx : BinaryBlueChoice.encode (listEnc enc) (some (q,xs))≠[] := by
            simp [BinaryBlueChoice.encode,WordList.encode,WordList.cons,pairBits]
          have hy : BinaryBlueChoice.encode (listEnc enc) (some (r,ys))≠[] := by
            simp [BinaryBlueChoice.encode,WordList.encode,WordList.cons,pairBits]
          rw [ite_eq_right hx,ite_eq_right hy]
          simp only [output,sum,extractPrefix_pairBits,discardPrefix_pairBits,BinaryBlueChoice.encode,
            WordList.encode,head_cons,extractPrefix_pairBits,BinaryBlueChoice.score,payload,
            discardPrefix_pairBits,BinaryRational.decode_encode,BlueDP.merge,listEnc_append]
end MetricKMedianRecovery.BitMachine.BinaryBlueMerge

namespace MetricKMedianRecovery.BlueDP
variable {A : Type*}
def score0 : Candidate (List A)→ℚ := fun x=>x.map Prod.fst |>.getD 0
def atoms : Candidate (List A)→List A := fun x=>x.map Prod.snd |>.getD []
lemma collect_formula (xs : List (Candidate (List A))) : collect xs =
    if xs.any Option.isNone then none else some ((xs.map score0).sum,xs.flatMap atoms) := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    change merge x (collect xs)=_
    rw [ih]
    cases x with
    | none=>simp [merge]
    | some x=>cases x; cases hb : xs.any Option.isNone <;> simp [merge,score0,atoms,hb]
end MetricKMedianRecovery.BlueDP
namespace MetricKMedianRecovery.BitMachine.BinaryBlueCollect
open WordOperations WordList
variable {A : Type*}
noncomputable def invalid (x : List Bool) : Bool := decide (discardPrefix x=[])
noncomputable def invalid_computes : PolyComputes (fun x=>[invalid x]) := discardPrefix_computes.comp isEmpty_computes
noncomputable def bad (x : List Bool) : List Bool := Find.run invalid (pairBits ([],x))
noncomputable def bad_computes : PolyComputes bad := ((const_computes []).pair id_computes).comp (Find.run_computes invalid_computes)
noncomputable def scoreOp (x : List Bool) : List Bool := BinaryBlueChoice.score (discardPrefix x)
noncomputable def scoreOp_computes : PolyComputes scoreOp := discardPrefix_computes.comp BinaryBlueChoice.score_computes
noncomputable def scores (x : List Bool) : List Bool := mapWith scoreOp (pairBits ([],x))
attribute [local irreducible] mapWith
noncomputable def scores_computes : PolyComputes scores :=
  PolyComputes.comp (f := fun input => pairBits ([],input)) (g := mapWith scoreOp)
    ((const_computes []).pair id_computes) (mapWith_computes scoreOp_computes)
noncomputable def payloadOp (x : List Bool) : List Bool := BinaryBlueMerge.payload (discardPrefix x)
noncomputable def payloadOp_computes : PolyComputes payloadOp := discardPrefix_computes.comp BinaryBlueMerge.payload_computes
noncomputable def contents (x : List Bool) : List Bool := flatMapWith payloadOp (pairBits ([],x))
noncomputable def contents_computes : PolyComputes contents := ((const_computes []).pair id_computes).comp (flatMapWith_computes payloadOp_computes)
noncomputable def result (x : List Bool) : List Bool := WordList.encode [pairBits (RationalArray.sumWords (scores x),contents x)]
noncomputable def result_computes : PolyComputes result :=
  cons_computes ((scores_computes.comp RationalArray.sumWords_computes).pair contents_computes) (const_computes [])
noncomputable def run (x : List Bool) : List Bool := if bad x=[] then result x else []
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def,decide_eq_true_eq] using
    (bad_computes.comp isEmpty_computes).cond result_computes (const_computes [])
lemma enc_empty (enc : A→List Bool) (x : BlueDP.Candidate (List A)) :
    BinaryBlueChoice.encode (BinaryBlueMerge.listEnc enc) x=[] ↔ x.isNone=true := by
  cases x with
  | none=>simp [BinaryBlueChoice.encode]
  | some x=>cases x;simp [BinaryBlueChoice.encode,WordList.encode,WordList.cons,pairBits]
lemma bad_empty (enc : A→List Bool) (xs : List (BlueDP.Candidate (List A))) :
    bad (WordList.encode (xs.map (BinaryBlueChoice.encode (BinaryBlueMerge.listEnc enc))))=[] ↔ xs.any Option.isNone=false := by
  simp only [bad,Find.run_encode]
  have ho (z : Option (List Bool)) : Find.optionEncode z=[] ↔ z=none := by cases z <;> simp [Find.optionEncode]
  rw [ho,List.find?_eq_none,List.any_eq_false]
  constructor
  · intro h x hx
    have hh:=h _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
    simpa only [invalid,discardPrefix_pairBits,decide_eq_true_eq,enc_empty] using hh
  · intro h w hw
    obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hw
    simpa only [invalid,discardPrefix_pairBits,decide_eq_true_eq,enc_empty] using h x hx
lemma score_some (enc : A→List Bool) (x : BlueDP.Candidate (List A)) (h : x.isNone=false) :
    BinaryBlueChoice.score (BinaryBlueChoice.encode (BinaryBlueMerge.listEnc enc) x)=BinaryRational.encode (BlueDP.score0 x) := by
  cases x with
  | none=>cases h
  | some x=>cases x;simp [BinaryBlueChoice.score,BinaryBlueChoice.encode,WordList.encode,BlueDP.score0]
lemma contents_pack (enc : A→List Bool) (xs : List (BlueDP.Candidate (List A))) :
    contents (WordList.encode (xs.map (BinaryBlueChoice.encode (BinaryBlueMerge.listEnc enc))))=
      BinaryBlueMerge.listEnc enc (xs.flatMap BlueDP.atoms) := by
  simp only [contents,flatMapWith,Function.comp_apply,mapWith_encode,List.map_map,Function.comp_def,
    payloadOp,discardPrefix_pairBits,Flatten.run_encode,BinaryBlueMerge.listEnc,List.map_flatMap,Flatten.encode_flatMap]
  congr 1
  apply List.map_congr_left
  intro x _
  cases x with
  | none=>simp [BinaryBlueMerge.payload,BinaryBlueChoice.encode,WordList.head,BlueDP.atoms,WordList.encode,extractPrefix,discardPrefix]
  | some x=>cases x;simp [BinaryBlueMerge.payload,BinaryBlueChoice.encode,WordList.encode,BlueDP.atoms,BinaryBlueMerge.listEnc]
lemma run_pack (enc : A→List Bool) (xs : List (BlueDP.Candidate (List A))) :
    run (WordList.encode (xs.map (BinaryBlueChoice.encode (BinaryBlueMerge.listEnc enc))))=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc enc) (BlueDP.collect xs) := by
  rw [BlueDP.collect_formula,run]
  cases h : xs.any Option.isNone with
  | true=>rw [ite_eq_right ((bad_empty enc xs).not.mpr (by simp [h]))];rfl
  | false=>
    rw [ite_eq_left ((bad_empty enc xs).mpr h)]
    simp only [Bool.false_eq_true,ite_false,BinaryBlueChoice.encode,result,contents_pack]
    congr 2
    have hs : scores (WordList.encode (xs.map (BinaryBlueChoice.encode (BinaryBlueMerge.listEnc enc))))=
        RationalArray.encode (xs.map BlueDP.score0) := by
      simp only [scores,mapWith_encode,List.map_map,Function.comp_def,scoreOp,discardPrefix_pairBits,RationalArray.encode]
      congr 1
      apply List.map_congr_left
      intro x hx
      exact score_some enc x (Bool.eq_false_iff.mpr ((List.any_eq_false.mp h) x hx))
    rw [hs,RationalArray.sumWords_encode]
end MetricKMedianRecovery.BitMachine.BinaryBlueCollect

end OAI
