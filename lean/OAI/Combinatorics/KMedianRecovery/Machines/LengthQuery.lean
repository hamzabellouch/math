import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.OrientedSearch
import OAI.Combinatorics.KMedianRecovery.Recovery.CrossCount

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLengthQuery
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryFiniteMachine.continuation

def ctxBits {m : ℕ} (base : List Bool) (n q key : ℕ) (root : Label (Fin m)) (b : ℚ)
    (T U : List (List (Label (Fin m)))) : List Bool :=
  encode [base,List.replicate n true,List.replicate q true,key.bits,BinaryLabel.encode root,BinaryRational.encode b,
    historyBits T,historyBits U]
def cf (n : ℕ) : List Bool→List Bool := field n ∘ extractPrefix
noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
noncomputable def newLeaf (x : List Bool) : List Bool :=
  pairBits ((value (cf 3 x)+1).bits,pairBits (BinaryLabel.parentWords (cf 4 x),discardPrefix x))
noncomputable def newLeaf_computes : PolyComputes newLeaf := by
  have hi : PolyComputes (fun x=>(value (cf 3 x)+1).bits) := by
    simpa only [value_bits] using NatOps.add (cf_computes 3) (const_computes (1:ℕ).bits)
  exact hi.pair (((cf_computes 4).comp BinaryLabel.parentWords_computes).pair discardPrefix_computes)
lemma newLeaf_pack {m : ℕ} (base : List Bool) (n q key : ℕ) (root : Label (Fin m)) (b s : ℚ)
    (T U : List (List (Label (Fin m)))) :
    newLeaf (pairBits (ctxBits base n q key root b T U,BinaryRational.encode s))=
      BinaryLabel.encode (leaf key (parent root) s) := by
  simp only [newLeaf,cf,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,ctxBits,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,
    BinaryLabel.parentWords_encode]
  rfl
noncomputable def opened (x : List Bool) : List Bool :=
  BinaryFiniteContext.union (pairBits (field 3 (cf 0 x),WordList.cons (newLeaf x) []))
noncomputable def opened_computes : PolyComputes opened :=
  (((cf_computes 0).comp (field_computes 3)).pair (cons_computes newLeaf_computes (const_computes []))).comp
    BinaryFiniteContext.union_computes
lemma opened_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (i : Label (Fin m)) (b s : ℚ)
    (T U : List (List (Label (Fin m)))) :
    opened (pairBits (ctxBits (BinaryFiniteContext.pack distance loc F Q v z lam) n q key i b T U,BinaryRational.encode s))=
      setBits (insert (leaf key (parent i) s) Q) := by
  unfold opened
  rw [newLeaf_pack]
  simp only [cf,Function.comp_apply,extractPrefix_pairBits,ctxBits,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFiniteContext.pack]
  rw [←BinaryFiniteContext.labels_nil,←BinaryFiniteContext.labels_cons,BinaryFiniteContext.union_list_pack]
  simp only [List.toFinset_cons,List.toFinset_nil,Finset.union_insert,Finset.union_empty]
noncomputable def base (x : List Bool) : List Bool := BinaryFiniteContext.replaceOpen (pairBits (cf 0 x,opened x))
noncomputable def base_computes : PolyComputes base := ((cf_computes 0).pair opened_computes).comp BinaryFiniteContext.replaceOpen_computes
noncomputable def interior (x : List Bool) : List Bool := BinaryFiniteMachine.continuation
  (pairBits (cf 1 x,pairBits (cf 2 x,base x)))
noncomputable def interior_computes : PolyComputes interior :=
  ((cf_computes 1).pair ((cf_computes 2).pair base_computes)).comp BinaryFiniteMachine.continuation_computes
lemma interior_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (i : Label (Fin m)) (b s : ℚ)
    (T U : List (List (Label (Fin m)))) :
    interior (pairBits (ctxBits (BinaryFiniteContext.pack distance loc F Q v z lam) n q key i b T U,BinaryRational.encode s))=
      historyBits (FiniteLabelContinuation.continuation loc (rows distance) F v lam q n (insert (leaf key (parent i) s) Q)) := by
  simp only [interior,base,opened_pack]
  simp only [cf,Function.comp_apply,extractPrefix_pairBits,ctxBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinaryFiniteContext.replaceOpen_pack,BinaryFiniteMachine.continuation_pack]
noncomputable def isZero (x : List Bool) : Bool := decide (BinaryRational.decode (discardPrefix x)=0)
noncomputable def isZero_computes : PolyComputes (fun x=>[isZero x]) := RatOps.eq (RatOps.ofWords discardPrefix_computes) (RatOps.const 0)
noncomputable def isUpper (x : List Bool) : Bool := decide (BinaryRational.decode (discardPrefix x)=BinaryRational.decode (cf 5 x))
noncomputable def isUpper_computes : PolyComputes (fun x=>[isUpper x]) := RatOps.eq (RatOps.ofWords discardPrefix_computes) (RatOps.ofWords (cf_computes 5))
noncomputable def chosen (x : List Bool) : List Bool := if isZero x then cf 6 x else if isUpper x then cf 7 x else interior x
noncomputable def chosen_computes : PolyComputes chosen := isZero_computes.cond (cf_computes 6)
  (isUpper_computes.cond (cf_computes 7) interior_computes)
lemma chosen_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (i : Label (Fin m)) (b s : ℚ)
    (T U : List (List (Label (Fin m)))) :
    chosen (pairBits (ctxBits (BinaryFiniteContext.pack distance loc F Q v z lam) n q key i b T U,BinaryRational.encode s))=
      historyBits (CanonicalLengthSearch.chosen
        (fun s=>FiniteLabelContinuation.continuation loc (rows distance) F v lam q n (insert (leaf key (parent i) s) Q)) T U b s) := by
  unfold chosen
  rw [interior_pack]
  simp only [isZero,isUpper,cf,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    ctxBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryRational.decode_encode,
    decide_eq_true_eq,CanonicalLengthSearch.chosen]
  split_ifs <;> rfl
noncomputable def finalOpened (x : List Bool) : List Bool := BinaryFiniteMachine.after (pairBits (opened x,chosen x))
noncomputable def finalOpened_computes : PolyComputes finalOpened :=
  (opened_computes.pair chosen_computes).comp BinaryFiniteMachine.after_computes
noncomputable def count (x : List Bool) : List Bool := BinaryFiniteContext.countInter (pairBits (finalOpened x,field 2 (cf 0 x)))
noncomputable def count_computes : PolyComputes count :=
  (finalOpened_computes.pair ((cf_computes 0).comp (field_computes 2))).comp BinaryFiniteContext.countInter_computes
lemma count_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (i : Label (Fin m)) (b s : ℚ)
    (T U : List (List (Label (Fin m)))) :
    count (pairBits (ctxBits (BinaryFiniteContext.pack distance loc F Q v z lam) n q key i b T U,BinaryRational.encode s))=
      (CanonicalLengthSearch.count F Q (leaf key (parent i))
        (fun s=>FiniteLabelContinuation.continuation loc (rows distance) F v lam q n (insert (leaf key (parent i) s) Q)) T U b s).bits := by
  simp only [count,finalOpened,opened_pack,chosen_pack,BinaryFiniteMachine.after_pack]
  simp only [cf,Function.comp_apply,extractPrefix_pairBits,ctxBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinaryFiniteContext.pack,BinaryFiniteContext.countInter_pack,
    CanonicalLengthSearch.count]
end MetricKMedianRecovery.BitMachine.BinaryLengthQuery

namespace MetricKMedianRecovery.BitMachine.BinaryLengthSearch
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
def resultBits {m : ℕ} : CanonicalLengthSearch.Result (Label (Fin m))→List Bool
  | .success s T=>encode [(0:ℕ).bits,BinaryRational.encode s,[],historyBits T,[]]
  | .bracket l u T U=>encode [(1:ℕ).bits,BinaryRational.encode l,BinaryRational.encode u,historyBits T,historyBits U]
def lower : List Bool→List Bool := extractPrefix ∘ discardPrefix
def upper : List Bool→List Bool := discardPrefix ∘ discardPrefix
noncomputable def lower_computes : PolyComputes lower := discardPrefix_computes.comp extractPrefix_computes
noncomputable def upper_computes : PolyComputes upper := discardPrefix_computes.comp discardPrefix_computes
def context : List Bool→List Bool := field 1 ∘ extractPrefix
noncomputable def context_computes : PolyComputes context := extractPrefix_computes.comp (field_computes 1)
def boundK : List Bool→List Bool := field 2 ∘ extractPrefix
noncomputable def boundK_computes : PolyComputes boundK := extractPrefix_computes.comp (field_computes 2)
def leftInput (x : List Bool) : List Bool := pairBits (context x,lower x)
def rightInput (x : List Bool) : List Bool := pairBits (context x,upper x)
noncomputable def leftInput_computes : PolyComputes leftInput := context_computes.pair lower_computes
noncomputable def rightInput_computes : PolyComputes rightInput := context_computes.pair upper_computes
noncomputable def leftHistory : List Bool→List Bool := BinaryLengthQuery.chosen ∘ leftInput
noncomputable def rightHistory : List Bool→List Bool := BinaryLengthQuery.chosen ∘ rightInput
noncomputable def leftHistory_computes : PolyComputes leftHistory := leftInput_computes.comp BinaryLengthQuery.chosen_computes
noncomputable def rightHistory_computes : PolyComputes rightHistory := rightInput_computes.comp BinaryLengthQuery.chosen_computes
noncomputable def leftSuccess (x : List Bool) : List Bool := encode [(0:ℕ).bits,lower x,[],leftHistory x,[]]
noncomputable def rightSuccess (x : List Bool) : List Bool := encode [(0:ℕ).bits,upper x,[],rightHistory x,[]]
noncomputable def bracket (x : List Bool) : List Bool := encode [(1:ℕ).bits,lower x,upper x,leftHistory x,rightHistory x]
noncomputable def leftSuccess_computes : PolyComputes leftSuccess :=
  list_computes [(fun _=>(0:ℕ).bits),lower,(fun _=>[]),leftHistory,(fun _=>[])] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨const_computes _⟩
    · exact ⟨lower_computes⟩
    · exact ⟨const_computes _⟩
    · exact ⟨leftHistory_computes⟩
    · exact ⟨const_computes _⟩)
noncomputable def rightSuccess_computes : PolyComputes rightSuccess :=
  list_computes [(fun _=>(0:ℕ).bits),upper,(fun _=>[]),rightHistory,(fun _=>[])] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨const_computes _⟩
    · exact ⟨upper_computes⟩
    · exact ⟨const_computes _⟩
    · exact ⟨rightHistory_computes⟩
    · exact ⟨const_computes _⟩)
noncomputable def bracket_computes : PolyComputes bracket :=
  list_computes [(fun _=>(1:ℕ).bits),lower,upper,leftHistory,rightHistory] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨const_computes _⟩
    · exact ⟨lower_computes⟩
    · exact ⟨upper_computes⟩
    · exact ⟨leftHistory_computes⟩
    · exact ⟨rightHistory_computes⟩)
noncomputable def leftEqual (x : List Bool) : Bool := decide (value (BinaryLengthQuery.count (leftInput x))=value (boundK x))
noncomputable def rightEqual (x : List Bool) : Bool := decide (value (BinaryLengthQuery.count (rightInput x))=value (boundK x))
noncomputable def leftEqual_computes : PolyComputes (fun x=>[leftEqual x]) :=
  NatOps.eq (leftInput_computes.comp BinaryLengthQuery.count_computes) boundK_computes
noncomputable def rightEqual_computes : PolyComputes (fun x=>[rightEqual x]) :=
  NatOps.eq (rightInput_computes.comp BinaryLengthQuery.count_computes) boundK_computes
noncomputable def finish (x : List Bool) : List Bool :=
  if leftEqual x then leftSuccess x else if rightEqual x then rightSuccess x else bracket x
noncomputable def finish_computes : PolyComputes finish := leftEqual_computes.cond leftSuccess_computes
  (rightEqual_computes.cond rightSuccess_computes bracket_computes)
lemma finish_pack (N : ℕ) (ctx : List Bool) (k : ℕ) (b l u : ℚ) :
    finish (pairBits (BinaryBisection.pack N ctx k 0 b,pairBits (BinaryRational.encode l,BinaryRational.encode u)))=
    if value (BinaryLengthQuery.count (pairBits (ctx,BinaryRational.encode l)))=k then
      encode [(0:ℕ).bits,BinaryRational.encode l,[],BinaryLengthQuery.chosen (pairBits (ctx,BinaryRational.encode l)),[]]
    else if value (BinaryLengthQuery.count (pairBits (ctx,BinaryRational.encode u)))=k then
      encode [(0:ℕ).bits,BinaryRational.encode u,[],BinaryLengthQuery.chosen (pairBits (ctx,BinaryRational.encode u)),[]]
    else encode [(1:ℕ).bits,BinaryRational.encode l,BinaryRational.encode u,
      BinaryLengthQuery.chosen (pairBits (ctx,BinaryRational.encode l)),BinaryLengthQuery.chosen (pairBits (ctx,BinaryRational.encode u))] := by
  simp only [finish,leftEqual,rightEqual,leftSuccess,rightSuccess,bracket,leftHistory,rightHistory,
    leftInput,rightInput,context,boundK,lower,upper,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    BinaryBisection.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,decide_eq_true_eq]
noncomputable def input (x : List Bool) : List Bool := pairBits (x,BinaryOrientedSearch.run BinaryLengthQuery.count x)
noncomputable def input_computes : PolyComputes input := id_computes.pair (BinaryOrientedSearch.run_computes BinaryLengthQuery.count_computes)
noncomputable def run : List Bool→List Bool := finish ∘ input
noncomputable def run_computes : PolyComputes run := input_computes.comp finish_computes
lemma run_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (i : Label (Fin m)) (b : ℚ)
    (T U : List (List (Label (Fin m)))) (k N : ℕ) :
    run (BinaryBisection.pack N (BinaryLengthQuery.ctxBits (BinaryFiniteContext.pack distance loc F Q v z lam) n q key i b T U) k 0 b)=
      resultBits (CanonicalLengthSearch.run F Q (leaf key (parent i))
        (fun s=>FiniteLabelContinuation.continuation loc (rows distance) F v lam q n (insert (leaf key (parent i) s) Q)) T U b k N) := by
  unfold run input
  rw [Function.comp_apply,BinaryOrientedSearch.run_pack]
  simp only [BinaryLengthQuery.count_pack,value_bits]
  rw [finish_pack]
  simp only [BinaryLengthQuery.count_pack,value_bits,BinaryLengthQuery.chosen_pack,CanonicalLengthSearch.run]
  split_ifs <;> rfl
end MetricKMedianRecovery.BitMachine.BinaryLengthSearch

end OAI
