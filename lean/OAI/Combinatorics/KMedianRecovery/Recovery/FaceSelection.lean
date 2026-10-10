import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.CoordinateRow
import OAI.Combinatorics.KMedianRecovery.Recovery.BoundedDecision

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryFace
open WordList
noncomputable def negEntry : List Bool → List Bool := BinaryRational.negWords ∘ discardPrefix
noncomputable def negEntry_computes : PolyComputes negEntry := discardPrefix_computes.comp BinaryRational.negWords_computes
noncomputable def reverse (x : List Bool) : List Bool :=
  pairBits (mapWith negEntry (pairBits ([],extractPrefix x)),BinaryRational.negWords (discardPrefix x))
noncomputable def reverse_computes : PolyComputes reverse := by
  unfold reverse
  simpa only [Function.comp_def] using
    (PolyComputes.pair (f:=mapWith negEntry ∘ (fun input=>pairBits ([],extractPrefix input)))
      (g:=BinaryRational.negWords ∘ discardPrefix)
      (PolyComputes.comp (f:=fun input=>pairBits ([],extractPrefix input)) (g:=mapWith negEntry)
        ((const_computes []).pair extractPrefix_computes) (mapWith_computes negEntry_computes))
      (discardPrefix_computes.comp BinaryRational.negWords_computes))
lemma reverse_encode {n : ℕ} (q : Row n) : reverse (BinaryRow.encode q)=BinaryRow.encode (reverseRow q) := by
  simp only [reverse,BinaryRow.encode,extractPrefix_pairBits,discardPrefix_pairBits,
    RationalMatrix.rowEncode_eq,mapWith_ofFn,negEntry,Function.comp_apply,
    BinaryRational.negWords_encode,reverseRow]
noncomputable def reverseOp : List Bool → List Bool := reverse ∘ discardPrefix
noncomputable def reverseOp_computes : PolyComputes reverseOp := discardPrefix_computes.comp reverse_computes
noncomputable def reverseRows (x : List Bool) : List Bool := mapWith reverseOp (pairBits ([],x))
noncomputable def reverseRows_computes : PolyComputes reverseRows := by
  unfold reverseRows
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],input)) (g:=mapWith reverseOp)
      ((const_computes []).pair id_computes) (mapWith_computes reverseOp_computes))
lemma reverseRows_encode {n : ℕ} (qs : List (Row n)) :
    reverseRows (BinaryRow.rowsEncode qs)=BinaryRow.rowsEncode (qs.map reverseRow) := by
  simp only [reverseRows,BinaryRow.rowsEncode,mapWith_encode,List.map_map,Function.comp_def,
    reverseOp,discardPrefix_pairBits,reverse_encode]
noncomputable def proposed (x : List Bool) : List Bool := cons (Find.item x) (Find.accum x)
noncomputable def proposed_computes : PolyComputes proposed := cons_computes Find.item_computes Find.accum_computes
noncomputable def faceWords (x : List Bool) : List Bool :=
  BinaryRationalDecision.rows (Find.context x)++proposed x++reverseRows (proposed x)
noncomputable def faceWords_computes : PolyComputes faceWords := by
  unfold faceWords
  simpa only [Function.comp_def] using
    (PolyComputes.append
      (f:=fun input=>(BinaryRationalDecision.rows ∘ Find.context) input++proposed input)
      (g:=reverseRows ∘ proposed)
      ((Find.context_computes.comp BinaryRationalDecision.rows_computes).append proposed_computes)
      (PolyComputes.comp (f:=proposed) (g:=reverseRows) proposed_computes reverseRows_computes))
lemma faceWords_pack {n : ℕ} (rows picked : List (Row n)) (B : ℕ) (q : Row n) :
    faceWords (pairBits (BinaryRationalDecision.pack rows B,pairBits (BinaryRow.encode q,BinaryRow.rowsEncode picked)))=
      BinaryRow.rowsEncode (faceRows rows (q::picked)) := by
  simp only [faceWords,Find.context,Find.item,Find.accum,Function.comp_apply,proposed,
    extractPrefix_pairBits,discardPrefix_pairBits,(BinaryRationalDecision.projections_pack rows B).2.2.2]
  change BinaryRow.rowsEncode rows++BinaryRow.rowsEncode (q::picked)++reverseRows (BinaryRow.rowsEncode (q::picked))=_
  rw [reverseRows_encode]
  simp only [faceRows,BinaryRow.rowsEncode,List.map_append,encode_append]
noncomputable def decisionInput (x : List Bool) : List Bool :=
  pairBits (BinaryRationalDecision.first (Find.context x),pairBits (Count.run (faceWords x),
    pairBits (BinaryRationalDecision.bound (Find.context x),faceWords x)))
noncomputable def decisionInput_computes : PolyComputes decisionInput :=
  (Find.context_computes.comp BinaryRationalDecision.first_computes).pair
    ((faceWords_computes.comp Count.run_computes).pair
      ((Find.context_computes.comp BinaryRationalDecision.bound_computes).pair faceWords_computes))
lemma decisionInput_pack {n : ℕ} (rows picked : List (Row n)) (B : ℕ) (q : Row n) :
    decisionInput (pairBits (BinaryRationalDecision.pack rows B,pairBits (BinaryRow.encode q,BinaryRow.rowsEncode picked)))=
      BinaryRationalDecision.pack (faceRows rows (q::picked)) B := by
  simp only [decisionInput,Find.context,extractPrefix_pairBits,
    (BinaryRationalDecision.projections_pack rows B).1,(BinaryRationalDecision.projections_pack rows B).2.2.1,
    faceWords_pack]
  simp only [BinaryRow.rowsEncode,Count.run_encode,List.length_map,BinaryRationalDecision.pack]
noncomputable def decision : List Bool → List Bool := BinaryRationalDecision.run ∘ decisionInput
noncomputable def decision_computes : PolyComputes decision := decisionInput_computes.comp BinaryRationalDecision.run_computes
noncomputable def op (x : List Bool) : List Bool := if (decision x).head?.getD false then proposed x else Find.accum x
noncomputable def op_computes : PolyComputes op :=
  (decision_computes.comp MetricKMedianRecovery.BitMachine.head_computes).cond proposed_computes Find.accum_computes
lemma operation_pack {n : ℕ} (rows picked : List (Row n)) (B : ℕ) (q : Row n) :
    Fold.operation op (BinaryRationalDecision.pack rows B) (BinaryRow.rowsEncode picked) (BinaryRow.encode q)=
      BinaryRow.rowsEncode (if boundedRationalDecide (faceRows rows (q::picked)) B then q::picked else picked) := by
  simp only [Fold.operation,op,decision,Function.comp_apply,decisionInput_pack,BinaryRationalDecision.run_pack,
    List.head?_cons,Option.getD_some,proposed,Find.item,Find.accum,extractPrefix_pairBits,discardPrefix_pairBits]
  split <;> rfl
lemma fold_op {n : ℕ} (rows todo picked : List (Row n)) (B : ℕ) :
    (todo.map BinaryRow.encode).foldl (Fold.operation op (BinaryRationalDecision.pack rows B)) (BinaryRow.rowsEncode picked)=
      BinaryRow.rowsEncode (selectFace rows B todo picked) := by
  induction todo generalizing picked with
  | nil => rfl
  | cons q todo ih =>
    rw [List.map_cons,List.foldl_cons,operation_pack]
    unfold selectFace
    split <;> exact ih _
lemma length_selectFace {n : ℕ} (rows todo picked : List (Row n)) (B : ℕ) :
    (BinaryRow.rowsEncode (selectFace rows B todo picked)).length≤
      (BinaryRow.rowsEncode todo).length+(BinaryRow.rowsEncode picked).length := by
  induction todo generalizing picked with
  | nil => simp only [selectFace,BinaryRow.rowsEncode,List.map_nil,encode,List.length_nil,Nat.zero_add,Nat.le_refl]
  | cons q todo ih =>
    unfold selectFace
    split
    · have hh := ih (q::picked)
      simp only [BinaryRow.rowsEncode,List.map_cons,encode,length_cons] at hh ⊢
      omega
    · have hh := ih picked
      simp only [BinaryRow.rowsEncode,List.map_cons,encode,length_cons] at hh ⊢
      omega
noncomputable def run : List Bool → List Bool := Fold.run op (4*Polynomial.X+4)
noncomputable def run_computes : PolyComputes run := Fold.run_computes op_computes (4*Polynomial.X+4)
lemma run_pack {n : ℕ} (rows todo picked : List (Row n)) (B : ℕ) :
    run (Fold.pack (BinaryRow.rowsEncode todo) (BinaryRationalDecision.pack rows B) (BinaryRow.rowsEncode picked))=
      BinaryRow.rowsEncode (selectFace rows B todo picked) := by
  unfold run
  rw [show BinaryRow.rowsEncode todo=encode (todo.map BinaryRow.encode) from rfl,
    Fold.run_encode op (4*Polynomial.X+4) (BinaryRationalDecision.pack rows B) (BinaryRow.rowsEncode picked)
      (todo.map BinaryRow.encode) ((BinaryRow.rowsEncode todo).length+(BinaryRow.rowsEncode picked).length)]
  · exact fold_op rows todo picked B
  · intro k
    rw [←List.map_take,fold_op]
    have hh := length_selectFace rows (todo.take k) picked B
    have ht := length_encode_take (todo.map BinaryRow.encode) k
    rw [←List.map_take] at ht
    exact hh.trans (Nat.add_le_add_right ht _)
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Fold.length_pack]
    change _≤4*(2*(BinaryRow.rowsEncode todo).length+2*(BinaryRationalDecision.pack rows B).length+(BinaryRow.rowsEncode picked).length+2)+4
    dsimp only [BinaryRow.rowsEncode] at *
    omega
end BinaryFace
namespace BinaryFinalFace
open WordList BinaryRationalDecision
noncomputable def shape (s : Bool) (x : List Bool) : List Bool :=
  BinaryEllipsoidInitial.run (pairBits (first x,BinaryRational.encode (if s then 1 else -1)))
noncomputable def shape_computes (s : Bool) : PolyComputes (shape s) := by
  unfold shape
  simpa only [Function.comp_def] using
    (PolyComputes.comp
      (f:=fun input=>pairBits (first input,BinaryRational.encode (if s then 1 else -1)))
      (g:=BinaryEllipsoidInitial.run)
      (first_computes.pair (const_computes (BinaryRational.encode (if s then 1 else -1))))
      BinaryEllipsoidInitial.run_computes)
lemma shape_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) (s : Bool) :
    shape s (pack rs B)=RationalMatrix.encode (fun i j : Fin n=>if j=i then (if s then 1 else -1) else 0) := by
  rw [shape,(projections_pack rs B).1]
  change BinaryEllipsoidInitial.run (BinaryEllipsoidInitial.pack n (if s then 1 else -1))=_
  rw [BinaryEllipsoidInitial.run_pack]
  congr 1
  ext i j
  simp only [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
  by_cases h : i=j
  · subst j; simp
  · simp [h,Ne.symm h]
noncomputable def box (s : Bool) (x : List Bool) : List Bool :=
  mapWith BinaryDecision.boundOp (pairBits (BinaryRational.encode (value (bound x)),shape s x))
noncomputable def box_computes (s : Bool) : PolyComputes (box s) := by
  unfold box
  simpa only [Function.comp_def] using
    (PolyComputes.comp
      (f:=fun input=>pairBits (BinaryRational.encode (value (bound input):ℚ),shape s input))
      (g:=mapWith BinaryDecision.boundOp)
      ((RatOps.nat bound_computes).pair (shape_computes s))
      (mapWith_computes BinaryDecision.boundOp_computes))
lemma box_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) (s : Bool) :
    box s (pack rs B)=BinaryRow.rowsEncode (List.ofFn (fun i : Fin n=>coordinateRow i (if s then 1 else -1) B)) := by
  simp only [box,(projections_pack rs B).2.2.1,value_bits,shape_pack,RationalMatrix.encode,
    mapWith_ofFn,BinaryDecision.boundOp_pair,BinaryRow.rowsEncode,List.map_ofFn,Function.comp_def,coordinateRow]
noncomputable def allRows (x : List Bool) : List Bool := rows x++(box true x++box false x)
noncomputable def allRows_computes : PolyComputes allRows := rows_computes.append ((box_computes true).append (box_computes false))
lemma allRows_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) :
    allRows (pack rs B)=BinaryRow.rowsEncode (withBox rs B) := by
  simp only [allRows,(projections_pack rs B).2.2.2,box_pack,withBox,boxRows,BinaryRow.rowsEncode,
    List.map_append,encode_append,Bool.false_eq_true,ite_true,ite_false]
noncomputable def context (x : List Bool) : List Bool :=
  pairBits (first x,pairBits (Count.run (allRows x),pairBits (bound x,allRows x)))
noncomputable def context_computes : PolyComputes context :=
  first_computes.pair ((allRows_computes.comp Count.run_computes).pair (bound_computes.pair allRows_computes))
lemma context_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) : context (pack rs B)=pack (withBox rs B) B := by
  simp only [context,(projections_pack rs B).1,(projections_pack rs B).2.2.1,allRows_pack]
  simp only [BinaryRow.rowsEncode,Count.run_encode,List.length_map,pack]
noncomputable def run (x : List Bool) : List Bool := BinaryFace.run (Fold.pack (allRows x) (context x) [])
noncomputable def run_computes : PolyComputes run :=
  (Fold.pack_computes allRows_computes context_computes (const_computes [])).comp BinaryFace.run_computes
lemma run_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) : run (pack rs B)=BinaryRow.rowsEncode (finalFace rs B) := by
  rw [run,allRows_pack,context_pack]
  exact BinaryFace.run_pack (withBox rs B) (withBox rs B) [] B
end BinaryFinalFace
end MetricKMedianRecovery.BitMachine

end OAI
