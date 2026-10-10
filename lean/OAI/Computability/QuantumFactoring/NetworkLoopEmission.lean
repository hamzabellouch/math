import Mathlib
import OAI.Computability.QuantumFactoring.BooleanFold
import OAI.Computability.QuantumFactoring.NetworkEmissionCombinators

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
lemma fold_budget_extra (f : Pack→Pack→Pack) (c : ℕ)
    (h : ∀a b,(f a b).val.budget=a.val.budget+b.val.budget+c)
    (xs : List Pack) (a : Pack) :
    (xs.foldl (fun b a=>f a b) a).val.budget=a.val.budget+(xs.map (fun s=>s.val.budget)).sum+c*xs.length:=by
  induction xs generalizing a with
  | nil=>simp
  | cons s xs ih=>rw [List.foldl_cons,ih,h,List.map_cons,List.sum_cons,List.length_cons];ring
namespace Emission
noncomputable def foldRightPack {f : Pack→Pack→Pack} (c : ℕ)
    (h : ∀a b,(f a b).val.budget=a.val.budget+b.val.budget+c)
    (p : Procedure (prodCode packCode packCode) packCode (fun x=>f x.1 x.2)) :
    Procedure (prodCode (listCode packCode) packCode) packCode (fun x=>x.1.foldr f x.2):=by
  let fold:=foldList emptyPack p (Polynomial.C 104*(Polynomial.C (c+1)*Polynomial.X+1)^2) (by
    intro xs a i
    have hh:=packCode_bound ((xs.take i).foldl (fun b a=>f a b) a)
    rw [fold_budget_extra f c h] at hh
    have hb:=packBudget_le_code a
    have hx:=(packBudgets_le_code (xs.take i)).trans (listCode_length_take_le packCode i xs)
    have hl:=(list_length_le_code packCode (xs.take i)).trans (listCode_length_take_le packCode i xs)
    have hm:=Nat.pow_le_pow_left (show a.val.budget+((xs.take i).map (fun s=>s.val.budget)).sum+c*(xs.take i).length+1≤
      (c+1)*((listCode packCode xs).length+(packCode a).length)+1 by nlinarith) 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    exact hh.trans (Nat.mul_le_mul_left _ hm))
  let input:=((listReverse packCode emptyPack).comp (first (listCode packCode) packCode)).pair
    (second (listCode packCode) packCode)
  exact (fold.comp input).congrFun (by intro x;exact List.foldl_reverse)
noncomputable def allPackP : Procedure (prodCode unaryCode (listCode packCode)) packCode
    (fun x=>x.2.foldr bandPack (constantPack x.1 true)):=by
  let start:=constantPackP.comp ((first unaryCode (listCode packCode)).pair (Procedure.constant _ boolCode true))
  exact (foldRightPack 4 (by intros;rfl) bandPackP).comp ((second unaryCode (listCode packCode)).pair start)
noncomputable def anyPackP : Procedure (prodCode unaryCode (listCode packCode)) packCode
    (fun x=>x.2.foldr borPack (constantPack x.1 false)):=by
  let start:=constantPackP.comp ((first unaryCode (listCode packCode)).pair (Procedure.constant _ boolCode false))
  exact (foldRightPack 13 (by intros;dsimp [borPack,bnotPack,bandPack,compPack,pairPack,nodePack];omega) borPackP).comp
    ((second unaryCode (listCode packCode)).pair start)
end Emission
lemma allPack_value {n : ℕ} (ps : List Pack) (fs : List (BooleanNetwork n 1))
    (h : List.Forall₂ (fun p f=>p.val.value=erase f) ps fs) :
    (ps.foldr bandPack (constantPack n true)).val.value=erase (BooleanNetwork.all fs):=by
  induction h with
  | nil=>exact constantPack_value n true
  | cons hp hs ih=>exact bandPack_value _ _ _ _ hp ih
lemma anyPack_value {n : ℕ} (ps : List Pack) (fs : List (BooleanNetwork n 1))
    (h : List.Forall₂ (fun p f=>p.val.value=erase f) ps fs) :
    (ps.foldr borPack (constantPack n false)).val.value=erase (BooleanNetwork.any fs):=by
  induction h with
  | nil=>exact constantPack_value n false
  | cons hp hs ih=>exact borPack_value _ _ _ _ hp ih
lemma ofFn_nat_eq_map {β : Type} (k : ℕ) (f : ℕ→β) :
    List.ofFn (fun i:Fin k=>f i.val)=(List.range k).map f:=by
  apply List.ext_getElem
  · simp
  · intro i hi hj;simp

namespace NetEmits
open BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {n m : α→ℕ}
lemma compInput {n m : β→ℕ} {f : ∀x,BooleanNetwork (n x) (m x)} {g : α→β}
    (hf : NetEmits eb f) (hg : BitStackProgram.Emits ea eb g) : NetEmits ea (fun x=>f (g x)):=by
  obtain ⟨p,hp,ep⟩:=hf
  exact ⟨fun x=>p (g x),hp.comp hg,fun x=>ep (g x)⟩
lemma rangePack {f : ∀x,ℕ→BooleanNetwork (n x) (m x)} {k : α→ℕ}
    (hf : NetEmits (prodCode unaryCode ea) (fun x=>f x.2 x.1)) (hk : BitStackProgram.Emits ea unaryCode k) :
    ∃p : α→List Pack, BitStackProgram.Emits ea (listCode packCode) p ∧
      ∀x,List.Forall₂ (fun p y=>p.val.value=erase y) (p x) ((List.range (k x)).map (f x)):=by
  obtain ⟨q,⟨hp⟩,ep⟩:=hf
  refine ⟨fun x=>(List.range (k x)).map (fun i=>q (i,x)),
    (ofProcedure (Procedure.tabulate (f:=fun x i=>q (i,x)) emptyPack hp)).comp (hk.pair (id ea)),?_⟩
  intro x
  dsimp only
  induction List.range (k x) with
  | nil=>exact .nil
  | cons i is ih=>exact .cons (ep (i,x)) ih
lemma allRange {f : ∀x,ℕ→BooleanNetwork (n x) 1} {k : α→ℕ}
    (hn : BitStackProgram.Emits ea unaryCode n)
    (hf : NetEmits (prodCode unaryCode ea) (fun x=>f x.2 x.1)) (hk : BitStackProgram.Emits ea unaryCode k) :
    NetEmits ea (fun x=>BooleanNetwork.all (List.ofFn (fun i:Fin (k x)=>f x i.val))):=by
  obtain ⟨p,hp,ep⟩:=rangePack hf hk
  refine ⟨fun x=>(p x).foldr bandPack (constantPack (n x) true),
    (ofProcedure Emission.allPackP).comp (hn.pair hp),?_⟩
  intro x;dsimp only;rw [ofFn_nat_eq_map (k x) (f x)];exact allPack_value _ _ (ep x)
lemma anyRange {f : ∀x,ℕ→BooleanNetwork (n x) 1} {k : α→ℕ}
    (hn : BitStackProgram.Emits ea unaryCode n)
    (hf : NetEmits (prodCode unaryCode ea) (fun x=>f x.2 x.1)) (hk : BitStackProgram.Emits ea unaryCode k) :
    NetEmits ea (fun x=>BooleanNetwork.any (List.ofFn (fun i:Fin (k x)=>f x i.val))):=by
  obtain ⟨p,hp,ep⟩:=rangePack hf hk
  refine ⟨fun x=>(p x).foldr borPack (constantPack (n x) false),
    (ofProcedure Emission.anyPackP).comp (hn.pair hp),?_⟩
  intro x;dsimp only;rw [ofFn_nat_eq_map (k x) (f x)];exact anyPack_value _ _ (ep x)
lemma vectorRange {f : ∀x,ℕ→BooleanNetwork (n x) 1} {k : α→ℕ}
    (hn : BitStackProgram.Emits ea unaryCode n)
    (hf : NetEmits (prodCode unaryCode ea) (fun x=>f x.2 x.1)) (hk : BitStackProgram.Emits ea unaryCode k) :
    NetEmits ea (fun x=>BooleanNetwork.vector (fun i:Fin (k x)=>f x i.val)):=by
  obtain ⟨q,⟨hp⟩,ep⟩:=hf
  refine ⟨fun x=>vectorPack (n x) ((List.range (k x)).map (fun i=>q (i,x))),
    (ofProcedure Emission.vectorPackP).comp (hn.pair ((ofProcedure (Procedure.tabulate (f:=fun x i=>q (i,x)) emptyPack hp)).comp (hk.pair (id ea)))),?_⟩
  intro x
  dsimp only
  rw [←ofFn_nat_eq_map (k x) (fun i=>q (i,x))]
  exact vectorPack_value _ _ (fun i=>ep (i.val,x))
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
