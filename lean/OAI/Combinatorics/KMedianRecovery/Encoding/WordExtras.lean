import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.FiniteMachine

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordEq
lemma value_length_injective {xs ys : List Bool} (hl : xs.length=ys.length) (hv : value xs=value ys) : xs=ys := by
  induction xs generalizing ys with
  | nil=>exact (List.eq_nil_of_length_eq_zero hl.symm).symm
  | cons b xs ih=>
    cases ys with
    | nil=>simp only [List.length_cons,List.length_nil] at hl; omega
    | cons c ys=>
      have ht : xs.length=ys.length := by simpa only [List.length_cons,Nat.add_left_inj] using hl
      have hbc : b=c := by
        cases b <;> cases c <;> simp only [value,Bool.toNat_false,Bool.toNat_true] at hv ⊢ <;> omega
      subst c
      congr 1
      apply ih ht
      simp only [value] at hv
      omega
noncomputable def eq (x : List Bool) : Bool := decide (extractPrefix x=discardPrefix x)
noncomputable def eq_computes : PolyComputes (fun x=>[eq x]) := by
  have h:= (NatOps.eq extractPrefix_computes discardPrefix_computes).and
    (NatOps.eq (extractPrefix_computes.comp UnaryResources.lengthBits_computes)
      (discardPrefix_computes.comp UnaryResources.lengthBits_computes))
  convert h using 1
  funext x
  simp only [eq,Function.comp_apply,UnaryResources.lengthBits_eq,value_bits,←Bool.decide_and]
  congr 1
  apply decide_eq_decide.mpr
  constructor
  · intro he; rw [he]; exact ⟨rfl,rfl⟩
  · intro he; exact value_length_injective he.2 he.1
lemma eq_pair (xs ys : List Bool) : eq (pairBits (xs,ys))=decide (xs=ys) := by
  simp only [eq,extractPrefix_pairBits,discardPrefix_pairBits]
end WordEq
namespace WordList
lemma encode_injective : Function.Injective encode := by
  intro xs
  induction xs with
  | nil=>
    intro ys he
    cases ys with
    | nil=>rfl
    | cons y ys=>exact (cons_ne_nil y (encode ys) he.symm).elim
  | cons x xs ih=>
    intro ys he
    cases ys with
    | nil=>exact (cons_ne_nil x (encode xs) he).elim
    | cons y ys=>
      have hh:=congrArg head he
      have ht:=congrArg tail he
      simp only [encode,head_cons] at hh
      simp only [encode,tail_cons] at ht
      exact congrArg₂ List.cons hh (ih ht)
namespace Drop
open Lookup (step step_computes iterate_bounds step_zero step_succ)
def run (x : List Bool) : List Bool := discardPrefix (step^[x.length] x)
noncomputable def run_computes : PolyComputes run := by
  have hi := BoundedIteration.polynomialRun_computes step_computes Polynomial.X (4*Polynomial.X+1)
  have hh := hi.comp discardPrefix_computes
  have he (x : List Bool) : BoundedIteration.polynomialRun step Polynomial.X (4*Polynomial.X+1) x=
      step^[x.length] x := by
    have ht := BoundedIteration.polynomialRun_eq step Polynomial.X (4*Polynomial.X+1) x (by
      intro j _
      have hb := (iterate_bounds x j).2.2
      obtain ⟨hf,hr⟩ := ProductBits.projections_length x
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
        Polynomial.eval_one]
      omega)
    simpa only [Polynomial.eval_X] using ht
  change PolyComputes (fun x=>discardPrefix (step^[x.length] x))
  simpa only [Function.comp_def,he] using hh
lemma drop_iterate (n i : ℕ) (ws : List (List Bool)) (hn : ws.length≤n) :
    discardPrefix (step^[n] (pairBits (i.bits,encode ws)))=encode (ws.drop i) := by
  induction n generalizing i ws with
  | zero=>
    have hw : ws=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst ws
    simp only [Function.iterate_zero_apply,discardPrefix_pairBits,List.drop_nil]
  | succ n ih=>
    cases i with
    | zero=>rw [Function.iterate_fixed (step_zero ws),discardPrefix_pairBits,List.drop_zero]
    | succ i=>
      rw [Function.iterate_succ_apply,step_succ]
      have hl : ws.tail.length≤n := by simp only [List.length_tail]; omega
      rw [ih i ws.tail hl]
      cases ws with
      | nil=>simp only [List.tail_nil,List.drop_nil]
      | cons w ws=>rfl
lemma run_encode (i : ℕ) (ws : List (List Bool)) :
    run (pairBits (i.bits,encode ws))=encode (ws.drop i) := by
  apply drop_iterate
  have h:=length_le_encode ws
  rw [pairBits_length]
  dsimp only
  omega
end Drop
noncomputable def lengthBits : List Bool → List Bool := UnaryResources.lengthBits ∘ Count.run
noncomputable def lengthBits_computes : PolyComputes lengthBits := Count.run_computes.comp UnaryResources.lengthBits_computes
lemma lengthBits_encode (ws : List (List Bool)) : lengthBits (encode ws)=ws.length.bits := by
  simp only [lengthBits,Function.comp_apply,Count.run_encode,UnaryResources.lengthBits_eq,List.length_replicate]
end WordList
end MetricKMedianRecovery.BitMachine

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves
lemma labels_injective {m : ℕ} : Function.Injective (@labels m) := by
  intro A B h
  apply List.map_injective_iff.mpr BinaryLabel.encode_injective
  exact WordList.encode_injective h
lemma eq_labels {m : ℕ} (A B : List (Label (Fin m))) :
    WordEq.eq (pairBits (labels A,labels B))=decide (A=B) := by
  rw [WordEq.eq_pair]
  exact decide_eq_decide.mpr labels_injective.eq_iff
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext
namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations WordList RationalLeaves
noncomputable def missing (x : List Bool) : Bool := !contains (pairBits (discardPrefix x,extractPrefix x))
noncomputable def missing_computes : PolyComputes (fun x=>[missing x]) :=
  ((discardPrefix_computes.pair extractPrefix_computes).comp contains_computes).not
noncomputable def allIn (x : List Bool) : Bool := decide (Find.run missing x=[])
noncomputable def allIn_computes : PolyComputes (fun x=>[allIn x]) :=
  (Find.run_computes missing_computes).comp isEmpty_computes
lemma allIn_pack {m : ℕ} (F : Finset (Label (Fin m))) (A : List (Label (Fin m))) :
    allIn (pairBits (BinaryFiniteContext.setBits F,BinaryFiniteContext.labels A))=decide (∀ a∈A,a∈F) := by
  simp only [allIn,BinaryFiniteContext.setBits,BinaryFiniteContext.labels,Find.run_encode,
    BinaryOpeningActivity.optionEncode_nil_iff,List.find?_eq_none,List.mem_map,forall_exists_index,and_imp,
    forall_apply_eq_imp_iff₂,missing,extractPrefix_pairBits,discardPrefix_pairBits,contains_encode,
    Bool.not_eq_true]
  congr 1
  apply propext
  simp only [Bool.not_eq,ne_eq,Bool.not_eq_false,decide_eq_true_eq,orderedSort,Finset.mem_sort]
lemma contains_setBits {m : ℕ} (a : Label (Fin m)) (F : Finset (Label (Fin m))) :
    contains (pairBits (encode a,BinaryFiniteContext.setBits F))=decide (a∈F) := by
  simp only [BinaryFiniteContext.setBits,BinaryFiniteContext.labels,contains_encode,orderedSort,Finset.mem_sort]
end MetricKMedianRecovery.BitMachine.BinaryLabel
namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
def jumpBits {m : ℕ} : Jump (Label (Fin m)) → List Bool
  | .add i=>encode [(0:ℕ).bits,[],[],[],BinaryLabel.encode i]
  | .remove C T A i=>encode [(1:ℕ).bits,labels C,labels T,labels A,BinaryLabel.encode i]
  | .replace C T i=>encode [(2:ℕ).bits,labels C,labels T,[],BinaryLabel.encode i]
def ctxBits {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key : ℕ)
    (H G : List (Label (Fin m))) : List Bool := encode [setBits F,labels R,key.bits,labels H,labels G]
def cf (n : ℕ) : List Bool → List Bool := field n ∘ extractPrefix
def jf (n : ℕ) : List Bool → List Bool := field n ∘ discardPrefix
noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
noncomputable def jf_computes (n : ℕ) : PolyComputes (jf n) := discardPrefix_computes.comp (field_computes n)
noncomputable def tagIs (n : ℕ) (x : List Bool) : Bool := decide (value (jf 0 x)=n)
noncomputable def tagIs_computes (n : ℕ) : PolyComputes (fun x=>[tagIs n x]) := by
  simpa only [tagIs,value_bits] using NatOps.eq (jf_computes 0) (const_computes n.bits)
noncomputable def copied (x : List Bool) : List Bool := BinaryLabel.copied (pairBits (cf 2 x,jf 4 x))
noncomputable def copied_computes : PolyComputes copied := by
  have copiedComputes := ((cf_computes 2).pair (jf_computes 4)).comp BinaryLabel.copied_computes
  unfold copied
  simpa only [Function.comp_def] using copiedComputes
noncomputable def source (x : List Bool) : List Bool :=
  if tagIs 0 x then cf 3 x else jf 1 x++cons (if tagIs 1 x then jf 4 x else copied x) (jf 2 x)
noncomputable def source_computes : PolyComputes source :=
  (tagIs_computes 0).cond (cf_computes 3)
    ((jf_computes 1).append (cons_computes ((tagIs_computes 1).cond (jf_computes 4) copied_computes) (jf_computes 2)))
noncomputable def target (x : List Bool) : List Bool :=
  if tagIs 0 x then cf 3 x++cons (copied x) [] else
    if tagIs 1 x then (jf 1 x++jf 2 x)++jf 3 x else jf 1 x++cons (jf 4 x) (jf 2 x)
noncomputable def target_computes : PolyComputes target :=
  (tagIs_computes 0).cond ((cf_computes 3).append (cons_computes copied_computes (const_computes [])))
    ((tagIs_computes 1).cond (((jf_computes 1).append (jf_computes 2)).append (jf_computes 3))
      ((jf_computes 1).append (cons_computes (jf_computes 4) (jf_computes 2))))
noncomputable def labelsCheck (x : List Bool) : Bool :=
  if tagIs 1 x then BinaryLabel.allIn (pairBits (cf 0 x,jf 3 x)) else true
noncomputable def labelsCheck_computes : PolyComputes (fun x=>[labelsCheck x]) := by
  have h:=(tagIs_computes 1).cond (((cf_computes 0).pair (jf_computes 3)).comp BinaryLabel.allIn_computes)
    (const_computes [true])
  convert h using 1
  funext x
  unfold labelsCheck
  split_ifs <;> rfl
noncomputable def accepts (x : List Bool) : Bool :=
  WordEq.eq (pairBits (source x,cf 3 x)) && (WordEq.eq (pairBits (target x,cf 4 x)) &&
    (BinaryLabel.contains (pairBits (jf 4 x,cf 0 x)) &&
      labelsCheck x))
noncomputable def accepts_computes : PolyComputes (fun x=>[accepts x]) :=
  ((source_computes.pair (cf_computes 3)).comp WordEq.eq_computes).and
    (((target_computes.pair (cf_computes 4)).comp WordEq.eq_computes).and
      ((((jf_computes 4).pair (cf_computes 0)).comp BinaryLabel.contains_computes).and
        labelsCheck_computes))
lemma source_pack {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key : ℕ)
    (H G : List (Label (Fin m))) (J : Jump (Label (Fin m))) :
    source (pairBits (ctxBits F R key H G,jumpBits J))=labels (J.source (copy key) H) := by
  cases J <;> simp only [source,tagIs,copied,cf,jf,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    ctxBits,jumpBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,
    BinaryLabel.copied_pack,Jump.source,
    BinaryFiniteContext.labels_append,BinaryFiniteContext.labels_cons] <;> simp
lemma target_pack {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key : ℕ)
    (H G : List (Label (Fin m))) (J : Jump (Label (Fin m))) :
    target (pairBits (ctxBits F R key H G,jumpBits J))=labels (J.target (copy key) H) := by
  cases J <;> simp only [target,tagIs,copied,cf,jf,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    ctxBits,jumpBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,
    BinaryLabel.copied_pack,Jump.target,
    BinaryFiniteContext.labels_append,BinaryFiniteContext.labels_cons,BinaryFiniteContext.labels_nil] <;> simp
lemma accepts_pack {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key : ℕ)
    (H G : List (Label (Fin m))) (J : Jump (Label (Fin m))) :
    accepts (pairBits (ctxBits F R key H G,jumpBits J))=decide (CanonicalMergeRefinement.accepts F (copy key) H G J) := by
  apply Bool.eq_iff_iff.mpr
  simp only [accepts,source_pack,target_pack,Bool.and_eq_true]
  cases J <;> simp only [tagIs,labelsCheck,cf,jf,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    ctxBits,jumpBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    value_bits,BinaryFiniteContext.eq_labels,BinaryLabel.allIn_pack,
    BinaryLabel.contains_setBits,decide_eq_true_eq] <;>
    simp [CanonicalMergeRefinement.accepts,Jump.source,Jump.target,Jump.labels,List.append_assoc]

end MetricKMedianRecovery.BitMachine.BinaryJump

end OAI
