import Mathlib
import OAI.Computability.MinUncut.Search.ArithmeticExpression

namespace OAI

section
noncomputable section
namespace MinUncut.Costed
open Turing.ToPartrec Polynomial

namespace PolyProgram

def variableDrop : PolyProgram (fun v=>v.tail.drop v.headI) where
  code := dynamicDrop
  bound := C 3000*(X+1)^2
  run v := by
    cases v with
    | nil =>
      obtain ⟨t,ht,hc⟩ := run_caseZero (g:=.cons (.comp .succ .zero)
         (.cons .head (.comp .tail .tail))) (v:=[]) rfl (run_zero [])
      exact ⟨_,by norm_num [magnitude] at ht ⊢; omega,CodeRun.fixDone (u := [0]) hc rfl⟩
    | cons n v =>
      apply (run_dynamicDrop n v).mono
      simp only [eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_one]
      have hn : n+1≤ magnitude (n::v)+1 := by simp only [magnitude_cons]; omega
      nlinarith
  size v := by
    have h := (magnitude_drop v.headI v.tail).trans (magnitude_tail v)
    simp only [eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_one]
    nlinarith

def expressions {g : List ℕ → List ℕ} (G : PolyProgram g) :
    (es : List AExpr) → PolyProgram (fun v=>es.map (fun e=>e.eval v)++g v)
  | [] => G
  | e::es => e.program.cons (expressions G es)

end PolyProgram

namespace Blocks

def block (es : List AExpr) (i : ℕ) (v : List ℕ) : List ℕ := es.map (fun e=>e.eval (i::v))
def source (v : List ℕ) : List ℕ := v.drop (v.tail.headI+2)
def step (es : List AExpr) (v : List ℕ) : List ℕ :=
  (v.headI+1)::(v.tail.headI+es.length)::(block es v.headI (source v)++v.drop 2)

def extractor : PolyProgram (fun v=>v.headI::source v) :=
  PolyProgram.head.cons ((PolyProgram.variableDrop.comp
    ((PolyProgram.addOf (PolyProgram.projection 1) (PolyProgram.const 2)).cons PolyProgram.id)).ofEq
      (by intro v; simp only [Function.comp_def,List.headI_cons,List.tail_cons,List.drop_one,source]))

def stepProgram (es : List AExpr) : PolyProgram (step es) :=

  let pref : PolyProgram (fun v=>block es v.headI (source v)++v.drop 2) := by
    let rec go (l : List AExpr) : PolyProgram (fun v=> l.map (fun e=>e.eval (v.headI::source v))++v.drop 2) :=
      match l with
      | [] => PolyProgram.drop 2
      | e::l => (e.program.comp extractor).cons (go l)
    exact go es
  (PolyProgram.succ.cons
    ((PolyProgram.addOf (PolyProgram.projection 1) (PolyProgram.const es.length)).cons pref)).ofEq
      (by intro v; simp only [List.headI_cons,List.drop_one,step])

@[simp] lemma length_block (es : List AExpr) (i : ℕ) (v : List ℕ) :
    (block es i v).length=es.length := by simp [block]

lemma source_step (es : List AExpr) (v : List ℕ) : source (step es v)=source v := by
  simp only [source,step,List.drop_succ_cons,List.headI_cons,List.tail_cons]
  rw [show v.tail.headI+es.length=es.length+v.tail.headI by omega,← List.drop_drop]
  rw [← length_block es v.headI (v.drop (v.tail.headI+2)),List.drop_left]
  rw [List.drop_drop]
  congr 1
  omega

@[simp] lemma head_step (es : List AExpr) (v : List ℕ) : (step es v).headI=v.headI+1 := rfl
@[simp] lemma second_step (es : List AExpr) (v : List ℕ) : (step es v).tail.headI=v.tail.headI+es.length := rfl

lemma iterate_head (es : List AExpr) (v : List ℕ) (i : ℕ) :
    ((step es)^[i] v).headI=v.headI+i := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply',head_step,ih]; omega
lemma iterate_source (es : List AExpr) (v : List ℕ) (i : ℕ) :
    source ((step es)^[i] v)=source v := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply',source_step,ih]

lemma magnitude_append (v w : List ℕ) : magnitude (v++w)=magnitude v+magnitude w := by
  induction v with
  | nil => simp only [List.nil_append,magnitude_nil,Nat.zero_add]
  | cons a v ih => simp only [List.cons_append,magnitude_cons,ih]; omega

lemma magnitude_step (es : List AExpr) (v : List ℕ) :
    magnitude (step es v)≤ magnitude v+es.length+3+magnitude (block es v.headI (source v)) := by
  simp only [step,magnitude_cons,magnitude_append]
  cases v with
  | nil => simp [magnitude]; omega
  | cons a v =>
    cases v with
    | nil => simp [magnitude]; omega
    | cons b v => simp only [List.headI_cons,List.tail_cons,List.drop_succ_cons,List.drop_zero,magnitude_cons]; omega

lemma iterate_size (es : List AExpr) (v : List ℕ) (n i : ℕ) (hi : i≤n) :
    magnitude ((step es)^[i] v)≤ magnitude v+
      i*(es.length+3+((PolyProgram.expressions PolyProgram.nil es).bound).eval
        (n+1+2*magnitude v)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hh := ih (by omega)
    have hs := magnitude_step es ((step es)^[i] v)
    have hb := (PolyProgram.expressions PolyProgram.nil es).size
      (((step es)^[i] v).headI::source ((step es)^[i] v))
    change magnitude (block es _ _++[])≤_ at hb
    rw [List.append_nil,iterate_head,iterate_source] at hb
    have hm : magnitude ((v.headI+i)::source v)≤n+1+2*magnitude v := by
      have h1 := magnitude_head v
      have h2 := magnitude_drop (v.tail.headI+2) v
      simp only [magnitude_cons,source]
      omega
    have hb' := hb.trans (evalNat_mono _ hm)
    rw [iterate_head,iterate_source] at hs
    rw [Function.iterate_succ_apply']
    nlinarith

def iterationProgram (es : List AExpr) :
    PolyProgram (fun v=>(step es)^[v.headI] v.tail) :=
  PolyProgram.iterate (stepProgram es)
    (X+X*(C (es.length+3)+(PolyProgram.expressions PolyProgram.nil es).bound.comp (C 3*X+1))) (by
      intro n v i hi
      have h := iterate_size es v n i hi
      have hv : magnitude v≤ magnitude (n::v) := by simp only [magnitude_cons]; omega
      have hi' : i≤ magnitude (n::v) := by simp only [magnitude_cons]; omega
      have hn : n+1+2*magnitude v≤3*magnitude (n::v)+1 := by simp only [magnitude_cons]; omega
      have hb := evalNat_mono (PolyProgram.expressions PolyProgram.nil es).bound hn
      simp only [eval_add,eval_mul,eval_C,eval_comp,eval_X,eval_one]
      exact h.trans (Nat.add_le_add hv (Nat.mul_le_mul hi' (Nat.add_le_add_left hb _))))

lemma iterate_accumulator (es : List AExpr) (v : List ℕ) (n : ℕ) :
    (step es)^[n] (0::0::v)=n::(n*es.length)::
      ((List.range n).reverse.flatMap (fun i=>block es i v)++v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    have hs : source (n::(n*es.length)::((List.range n).reverse.flatMap (fun i=>block es i v)++v))=v := by
      rw [← ih,iterate_source]
      rfl
    simp only [step,List.headI_cons,List.tail_cons,hs,List.drop_succ_cons,List.drop_zero,
      List.range_succ,List.reverse_append,List.reverse_singleton,List.flatMap_append,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
    simp only [Nat.add_mul,Nat.one_mul]

def enumerate (es : List AExpr) (N : AExpr) : PolyProgram (fun v=>
    N.eval v::(N.eval v*es.length)::
      ((List.range (N.eval v)).reverse.flatMap (fun i=>block es i v)++v)) :=
  ((iterationProgram es).comp (N.program.cons ((PolyProgram.const 0).cons
    ((PolyProgram.const 0).cons PolyProgram.id)))).ofEq (by
      intro v
      change (step es)^[N.eval v] (0::0::v)=_
      exact iterate_accumulator es v (N.eval v))

end Blocks
end MinUncut.Costed

end
end

end OAI
