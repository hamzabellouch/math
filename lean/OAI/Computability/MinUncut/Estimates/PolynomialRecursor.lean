import Mathlib
import OAI.Computability.MinUncut.Estimates.CodeIteration
import OAI.Computability.MinUncut.Search.PolynomialArithmetic

namespace OAI

noncomputable section
namespace MinUncut.Costed.PolyProgram
open Turing.ToPartrec Polynomial

def scalarRec (f g : List ℕ → List ℕ) (v : List ℕ) : ℕ → ℕ
  | 0 => (f v).headI
  | i+1 => (g (i::scalarRec f g v i::v)).headI

def prec {f g : List ℕ → List ℕ} (F : PolyProgram f) (G : PolyProgram g)
    (p : Polynomial ℕ)
    (hs : ∀n v i,i≤n → scalarRec f g v i≤p.eval (magnitude (n::v))) :
    PolyProgram (fun v=>[scalarRec f g v.tail v.headI]) := by
  let F' := head.comp F
  let G' := head.comp G
  let P : PolyProgram (fun v=>v.headI::v.tail) := head.cons tail
  let W := X+1+p
  let B := F'.bound+(X+2)*(G'.bound.comp (C 3*W+3)+C 50000*(W+1))
  refine ⟨.comp (.prec F'.code G'.code) P.code,
    P.bound+B.comp P.bound+1+p.comp P.bound+1,?_,?_⟩
  · intro v
    let n := v.headI
    let u := v.tail
    let s := magnitude (n::u)
    let M := W.eval s
    have hn : n≤M := by simp [M,W,s,magnitude_cons]; omega
    have hu : magnitude u≤M := by simp [M,W,s,magnitude_cons]; omega
    have hr : ∀i≤n,scalarRec f g u i≤M := by
      intro i hi
      have h : scalarRec f g u i≤p.eval s := hs n u i hi
      simp only [M,W,eval_add,eval_X,eval_one]
      omega
    have hf : Runs F'.code u [scalarRec f g u 0] (F'.bound.eval s) :=
      (F'.run u).mono (evalNat_mono _ (by simp only [s,magnitude_cons]; omega))
    have hg : ∀i<n,Runs G'.code (i::scalarRec f g u i::u)
        [scalarRec f g u (i+1)] (G'.bound.eval (3*M+3)) := by
      intro i hi
      apply (G'.run _).mono
      apply evalNat_mono
      have h := hr i (by omega)
      simp only [magnitude_cons]; omega
    have hh := run_prec F'.code G'.code n (scalarRec f g u) u M
      (F'.bound.eval s) (G'.bound.eval (3*M+3)) hn hr hu hf hg
    have hh' : Runs (.prec F'.code G'.code) (n::u) [scalarRec f g u n] (B.eval s) := by
      apply hh.mono
      simp only [B,eval_add,eval_mul,eval_comp,eval_C,eval_X,eval_ofNat,eval_one]
      have hn' : n ≤ s := by simp only [s,magnitude_cons]; omega
      gcongr
    have hx := run_comp (P.run v) hh'
    apply hx.mono
    have hb := evalNat_mono B (P.size v)
    simp only [eval_add,eval_comp,eval_one]
    change B.eval s≤B.eval (P.bound.eval (magnitude v)) at hb
    omega
  · intro v
    have h := (hs v.headI v.tail v.headI le_rfl).trans
      (evalNat_mono p (P.size v))
    simp only [magnitude_cons,magnitude_nil,eval_add,eval_comp,eval_one]
    omega

end MinUncut.Costed.PolyProgram

end
namespace MinUncut.Costed
inductive Expr where
  | const (n : ℕ)
  | reg (i : ℕ)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | eq (a b : Expr)
  | le (a b : Expr)
  | at (a : Expr)
  | cond (e a b : Expr)

def Expr.eval : Expr → List ℕ → ℕ
  | .const n,_ => n
  | .reg i,v => (v.drop i).headI
  | .add a b,v => a.eval v+b.eval v
  | .sub a b,v => a.eval v-b.eval v
  | .mul a b,v => a.eval v*b.eval v
  | .eq a b,v => if a.eval v=b.eval v then 1 else 0
  | .le a b,v => if a.eval v≤b.eval v then 1 else 0
  | .at a,v => (v.drop (a.eval v)).headI
  | .cond e a b,v => if e.eval v=0 then a.eval v else b.eval v

noncomputable def Expr.program : (e : Expr) → PolyProgram (fun v=>[e.eval v])
  | .const n => PolyProgram.const n
  | .reg i => PolyProgram.projection i
  | .add a b => PolyProgram.addOf a.program b.program
  | .sub a b => PolyProgram.subOf a.program b.program
  | .mul a b => PolyProgram.mulOf a.program b.program
  | .eq a b => PolyProgram.eqOf a.program b.program
  | .le a b => PolyProgram.leOf a.program b.program
  | .at a => PolyProgram.dynamic.comp (a.program.cons PolyProgram.id)
  | .cond e a b => (PolyProgram.branch e.program a.program b.program).ofEq (by
      intro v
      change (if e.eval v=0 then [a.eval v] else [b.eval v])=
        [if e.eval v=0 then a.eval v else b.eval v]
      by_cases h : e.eval v=0 <;> simp only [h,ite_true,ite_false])

def Expr.or (a b : Expr) : Expr := .cond a b (.const 1)
def Expr.edge (u v a b : Expr) : Expr :=
  (Expr.mul (.eq u a) (.eq v b)).or (.mul (.eq u b) (.eq v a))

lemma Expr.eval_or (a b : Expr) (v : List ℕ) :
    (a.or b).eval v=if a.eval v=0 then b.eval v else 1 := rfl
lemma Expr.eval_cond (e a b : Expr) (v : List ℕ) :
    (Expr.cond e a b).eval v=if e.eval v=0 then a.eval v else b.eval v := rfl
lemma Expr.eval_add (a b : Expr) (v : List ℕ) :
    (Expr.add a b).eval v=a.eval v+b.eval v := rfl
lemma Expr.eval_mul (a b : Expr) (v : List ℕ) :
    (Expr.mul a b).eval v=a.eval v*b.eval v := rfl
lemma Expr.eval_reg (i : ℕ) (v : List ℕ) : (Expr.reg i).eval v=(v.drop i).headI := rfl
lemma Expr.eval_const (n : ℕ) (v : List ℕ) : (Expr.const n).eval v=n := rfl

lemma Expr.eval_or_le_one (a b : Expr) (v : List ℕ) (hb : b.eval v≤1) :
    (a.or b).eval v≤1 := by simp only [Expr.or,Expr.eval]; split_ifs <;> omega
lemma Expr.eval_edge_le_one (u v a b : Expr) (w : List ℕ) :
    (Expr.edge u v a b).eval w≤1 := by
  apply Expr.eval_or_le_one
  simp only [Expr.eval]
  split_ifs <;> omega

lemma Expr.eval_edge (u v a b : Expr) (w : List ℕ) :
    (Expr.edge u v a b).eval w=
      if (u.eval w=a.eval w ∧ v.eval w=b.eval w) ∨
         (u.eval w=b.eval w ∧ v.eval w=a.eval w) then 1 else 0 := by
  simp only [Expr.edge,Expr.or,Expr.eval]
  split_ifs <;> omega

end MinUncut.Costed

namespace MinUncut.Costed.Arena

abbrev Node := Fin 4 → ℕ
abbrev Heap := List Node

def words (h : Heap) : List ℕ := h.flatMap (fun n => List.ofFn n)

def read (h : Heap) (a : ℕ) (j : Fin 4) : ℕ :=
  if a=0 then 0 else ((h.drop (h.length-a)).headD (fun _=>0)) j

@[simp] lemma words_nil : words []=[] := rfl
@[simp] lemma words_cons (n : Node) (h : Heap) :
    words (n::h)=[n 0,n 1,n 2,n 3]++words h := by
  simp [words,List.ofFn_succ]

@[simp] lemma length_words (h : Heap) : (words h).length=4*h.length := by
  induction h with
  | nil => rfl
  | cons n h ih => simp only [words_cons,List.length_append,List.length_cons,List.length_nil,ih]; omega

lemma words_drop (h : Heap) (i : ℕ) :
    (words h).drop (4*i)=words (h.drop i) := by
  induction i generalizing h with
  | zero => simp
  | succ i ih =>
    cases h with
    | nil => simp
    | cons n h =>
      rw [words_cons,show 4*(i+1)=4+4*i by omega,← List.drop_drop]
      simpa using ih h

lemma words_at (h : Heap) (i : ℕ) (j : Fin 4) :
    ((words h).drop (4*i+j.val)).headI=((h.drop i).headD (fun _=>0)) j := by
  rw [← List.drop_drop,words_drop]
  cases h.drop i with
  | nil => simp
  | cons n hs =>
    rw [words_cons]
    fin_cases j <;> rfl

lemma read_words (h : Heap) (a : ℕ) (j : Fin 4) :
    read h a j=if a=0 then 0 else ((words h).drop (4*(h.length-a)+j.val)).headI := by
  simp only [read,words_at]

@[simp] lemma read_null (h : Heap) (j : Fin 4) : read h 0 j=0 := by simp [read]

@[simp] lemma read_new (h : Heap) (n : Node) (j : Fin 4) :
    read (n::h) (h.length+1) j=n j := by simp [read]

lemma read_old (h : Heap) (n : Node) (a : ℕ) (ha : a≤h.length) (j : Fin 4) :
    read (n::h) a j=read h a j := by
  by_cases hz : a=0
  · simp [hz]
  · simp only [read,hz,ite_false,List.length_cons]
    rw [show h.length+1-a=(h.length-a)+1 by omega]
    rfl

def readExpr (pre len : ℕ) (addr : Expr) (field : Fin 4) : Expr :=
  .cond (.eq addr (.const 0))
    (.at (.add (.const (pre+field.val)) (.mul (.const 4) (.sub (.reg len) addr))))
    (.const 0)

lemma readExpr_eval (regs : List ℕ) (len : ℕ) (h : Heap) (addr : Expr) (field : Fin 4)
    (hlen : ((regs++words h).drop len).headI=h.length) :
    (readExpr regs.length len addr field).eval (regs++words h)=
      read h (addr.eval (regs++words h)) field := by
  rw [read_words]
  simp only [readExpr,Expr.eval,hlen]
  by_cases he : addr.eval (regs++words h)=0
  · simp [he]
  · simp only [he,ite_false,ite_true]
    rw [show regs.length+field.val+4*(h.length-addr.eval (regs++words h))=
        regs.length+(4*(h.length-addr.eval (regs++words h))+field.val) by omega]
    simp only [← List.drop_drop, List.drop_left]

lemma magnitude_words_le (h : Heap) (B : ℕ) (hh : ∀n∈h,∀j,n j≤B) :
    magnitude (words h)≤4*h.length*(B+1) := by
  induction h with
  | nil => simp
  | cons n h ih =>
    have hn := hh n (by simp)
    have ht := ih (fun m hm => hh m (by simp [hm]))
    simp only [words_cons,List.cons_append,List.nil_append,magnitude_cons,List.length_cons]
    have h0 := hn 0; have h1 := hn 1; have h2 := hn 2; have h3 := hn 3
    nlinarith

open Turing.ToPartrec

def node (a b c d : ℕ) : Node := ![a,b,c,d]

@[simp] lemma node_zero (a b c d : ℕ) : node a b c d 0=a := rfl
@[simp] lemma node_one (a b c d : ℕ) : node a b c d 1=b := rfl
@[simp] lemma node_two (a b c d : ℕ) : node a b c d 2=c := rfl
@[simp] lemma node_three (a b c d : ℕ) : node a b c d 3=d := rfl

inductive ListRep (h : Heap) : ℕ → List ℕ → Prop
  | nil : ListRep h 0 []
  | cons {p a q v} : 0<p → p≤h.length → read h p 0=a → read h p 1=q →
      ListRep h q v → ListRep h p (a::v)

lemma ListRep.bound {h p v} (hv : ListRep h p v) : p≤h.length := by
  cases hv with
  | nil => omega
  | cons _ hp => exact hp

lemma ListRep.head {h p v} (hv : ListRep h p v) : read h p 0=v.headI := by
  cases hv with
  | nil => simp
  | cons _ _ he => exact he

lemma ListRep.tail {h p v} (hv : ListRep h p v) : ListRep h (read h p 1) v.tail := by
  cases hv with
  | nil => simpa using ListRep.nil (h:=h)
  | cons _ _ _ he ht => simpa only [he,List.tail_cons] using ht

lemma ListRep.extend {h p v} (hv : ListRep h p v) (n : Node) : ListRep (n::h) p v := by
  induction hv with
  | nil => exact .nil
  | cons hpos hp ha hq hv ih =>
    exact .cons hpos (by simp only [List.length_cons]; omega)
      ((read_old h n _ hp 0).trans ha) ((read_old h n _ hp 1).trans hq) ih

lemma ListRep.push {h p v} (hv : ListRep h p v) (a : ℕ) :
    ListRep (node a p 0 0::h) (h.length+1) (a::v) := by
  refine .cons (by omega) (by simp) ?_ ?_ (hv.extend _)
  · simp [node]
  · simp [node]

inductive CodeAt (h : Heap) : ℕ → Code → Prop
  | zero {p} : 0<p → p≤h.length → read h p 0=0 → CodeAt h p .zero'
  | succ {p} : 0<p → p≤h.length → read h p 0=1 → CodeAt h p .succ
  | tail {p} : 0<p → p≤h.length → read h p 0=2 → CodeAt h p .tail
  | cons {p f fs} : 0<p → p≤h.length → read h p 0=3 →
      CodeAt h (read h p 1) f → CodeAt h (read h p 2) fs → CodeAt h p (.cons f fs)
  | comp {p f g} : 0<p → p≤h.length → read h p 0=4 →
      CodeAt h (read h p 1) f → CodeAt h (read h p 2) g → CodeAt h p (.comp f g)
  | case {p f g} : 0<p → p≤h.length → read h p 0=5 →
      CodeAt h (read h p 1) f → CodeAt h (read h p 2) g → CodeAt h p (.case f g)
  | fix {p f} : 0<p → p≤h.length → read h p 0=6 →
      CodeAt h (read h p 1) f → CodeAt h p (.fix f)

lemma CodeAt.bound {h p c} (hc : CodeAt h p c) : p≤h.length := by cases hc <;> assumption

lemma CodeAt.extend {h p c} (hc : CodeAt h p c) (n : Node) : CodeAt (n::h) p c := by
  induction hc with
  | zero hpos hp ht => exact .zero hpos (by simp; omega) ((read_old h n _ hp 0).trans ht)
  | succ hpos hp ht => exact .succ hpos (by simp; omega) ((read_old h n _ hp 0).trans ht)
  | tail hpos hp ht => exact .tail hpos (by simp; omega) ((read_old h n _ hp 0).trans ht)
  | cons hpos hp ht _ _ ih ih' =>
    exact .cons hpos (by simp; omega) ((read_old h n _ hp 0).trans ht)
      (by simpa only [read_old h n _ hp 1] using ih)
      (by simpa only [read_old h n _ hp 2] using ih')
  | comp hpos hp ht _ _ ih ih' =>
    exact .comp hpos (by simp; omega) ((read_old h n _ hp 0).trans ht)
      (by simpa only [read_old h n _ hp 1] using ih)
      (by simpa only [read_old h n _ hp 2] using ih')
  | case hpos hp ht _ _ ih ih' =>
    exact .case hpos (by simp; omega) ((read_old h n _ hp 0).trans ht)
      (by simpa only [read_old h n _ hp 1] using ih)
      (by simpa only [read_old h n _ hp 2] using ih')
  | fix hpos hp ht _ ih =>
    exact .fix hpos (by simp; omega) ((read_old h n _ hp 0).trans ht)
      (by simpa only [read_old h n _ hp 1] using ih)

lemma ListRep.prepend {h p v} (hv : ListRep h p v) (hs : Heap) : ListRep (hs++h) p v := by
  induction hs with
  | nil => exact hv
  | cons n hs ih => exact ih.extend n

lemma CodeAt.prepend {h p c} (hc : CodeAt h p c) (hs : Heap) : CodeAt (hs++h) p c := by
  induction hs with
  | nil => exact hc
  | cons n hs ih => exact ih.extend n

def codeCells : Code → ℕ → Heap
  | .zero',_ => [node 0 0 0 0]
  | .succ,_ => [node 1 0 0 0]
  | .tail,_ => [node 2 0 0 0]
  | .cons f g,b =>
    let l := codeCells f b
    let r := codeCells g (b+l.length)
    node 3 (b+l.length) (b+l.length+r.length) 0::(r++l)
  | .comp f g,b =>
    let l := codeCells f b
    let r := codeCells g (b+l.length)
    node 4 (b+l.length) (b+l.length+r.length) 0::(r++l)
  | .case f g,b =>
    let l := codeCells f b
    let r := codeCells g (b+l.length)
    node 5 (b+l.length) (b+l.length+r.length) 0::(r++l)
  | .fix f,b =>
    let l := codeCells f b
    node 6 (b+l.length) 0 0::l

lemma codeCells_spec (c : Code) (h : Heap) :
    CodeAt (codeCells c h.length++h) (h.length+(codeCells c h.length).length) c := by
  induction c generalizing h with
  | zero' => simpa [codeCells,node] using
      (CodeAt.zero (h := node 0 0 0 0::h) (p := h.length+1) (by omega) (by simp) (by simp [node]))
  | succ => simpa [codeCells,node] using
      (CodeAt.succ (h := node 1 0 0 0::h) (p := h.length+1) (by omega) (by simp) (by simp [node]))
  | tail => simpa [codeCells,node] using
      (CodeAt.tail (h := node 2 0 0 0::h) (p := h.length+1) (by omega) (by simp) (by simp [node]))
  | cons f g ih ih' =>
    simp only [codeCells,List.cons_append,List.length_cons,List.length_append]
    let l := codeCells f h.length
    let r := codeCells g (h.length+l.length)
    have hf := (ih h).prepend r
    have hg := ih' (l++h)
    simp only [List.length_append,Nat.add_comm l.length h.length] at hg
    change CodeAt (node 3 (h.length+l.length) (h.length+l.length+r.length) 0::((r++l)++h))
      (h.length+(r.length+l.length+1)) (.cons f g)
    have he : h.length+(r.length+l.length+1)=((r++l)++h).length+1 := by simp; omega
    rw [he]
    refine .cons (by omega) (by simp) (by rw [read_new]; rfl) ?_ ?_
    · simpa only [read_new,node_one,List.append_assoc] using hf.extend (node 3 (h.length+l.length) (h.length+l.length+r.length) 0)
    · simpa only [read_new,node_two,List.append_assoc] using hg.extend (node 3 (h.length+l.length) (h.length+l.length+r.length) 0)
  | comp f g ih ih' =>

    simp only [codeCells,List.cons_append,List.length_cons,List.length_append]
    let l := codeCells f h.length
    let r := codeCells g (h.length+l.length)
    have hf := (ih h).prepend r
    have hg := ih' (l++h)
    simp only [List.length_append,Nat.add_comm l.length h.length] at hg
    change CodeAt (node 4 (h.length+l.length) (h.length+l.length+r.length) 0::((r++l)++h))
      (h.length+(r.length+l.length+1)) (.comp f g)
    have he : h.length+(r.length+l.length+1)=((r++l)++h).length+1 := by simp; omega
    rw [he]
    refine .comp (by omega) (by simp) (by rw [read_new]; rfl) ?_ ?_
    · simpa only [read_new,node_one,List.append_assoc] using hf.extend (node 4 (h.length+l.length) (h.length+l.length+r.length) 0)
    · simpa only [read_new,node_two,List.append_assoc] using hg.extend (node 4 (h.length+l.length) (h.length+l.length+r.length) 0)
  | case f g ih ih' =>
    simp only [codeCells,List.cons_append,List.length_cons,List.length_append]
    let l := codeCells f h.length
    let r := codeCells g (h.length+l.length)
    have hf := (ih h).prepend r
    have hg := ih' (l++h)
    simp only [List.length_append,Nat.add_comm l.length h.length] at hg
    change CodeAt (node 5 (h.length+l.length) (h.length+l.length+r.length) 0::((r++l)++h))
      (h.length+(r.length+l.length+1)) (.case f g)
    have he : h.length+(r.length+l.length+1)=((r++l)++h).length+1 := by simp; omega
    rw [he]
    refine .case (by omega) (by simp) (by rw [read_new]; rfl) ?_ ?_
    · simpa only [read_new,node_one,List.append_assoc] using hf.extend (node 5 (h.length+l.length) (h.length+l.length+r.length) 0)
    · simpa only [read_new,node_two,List.append_assoc] using hg.extend (node 5 (h.length+l.length) (h.length+l.length+r.length) 0)
  | fix f ih =>
    simp only [codeCells,List.cons_append,List.length_cons]
    let l := codeCells f h.length
    change CodeAt (node 6 (h.length+l.length) 0 0::(l++h)) (h.length+(l.length+1)) (.fix f)
    rw [show h.length+(l.length+1)=(l++h).length+1 by simp; omega]
    refine .fix (by omega) (by simp) (by rw [read_new]; rfl) ?_
    simpa only [read_new,node_one] using (ih h).extend (node 6 (h.length+l.length) 0 0)

structure State where
  mode : ℕ
  pc : ℕ
  env : ℕ
  kont : ℕ
  heap : Heap

def State.encode (s : State) : List ℕ :=
  [s.mode,s.pc,s.env,s.kont,s.heap.length]++words s.heap

def State.tick (s : State) : State :=
  let h := s.heap
  let n := h.length
  let get := read h
  if s.mode=0 then
    match get s.pc 0 with
    | 0 => ⟨1,0,n+1,s.kont,node 0 s.env 0 0::h⟩
    | 1 => ⟨1,0,n+1,s.kont,node (get s.env 0+1) 0 0 0::h⟩
    | 2 => ⟨1,0,get s.env 1,s.kont,h⟩
    | 3 => ⟨0,get s.pc 1,s.env,n+1,node 0 (get s.pc 2) s.env s.kont::h⟩
    | 4 => ⟨0,get s.pc 2,s.env,n+1,node 2 (get s.pc 1) 0 s.kont::h⟩
    | 5 => if get s.env 0=0 then ⟨0,get s.pc 1,get s.env 1,s.kont,h⟩
        else ⟨0,get s.pc 2,n+1,s.kont,node (get s.env 0-1) (get s.env 1) 0 0::h⟩
    | 6 => ⟨0,get s.pc 1,s.env,n+1,node 3 s.pc 0 s.kont::h⟩
    | _ => ⟨2,0,s.env,0,h⟩
  else if s.mode=1 then
    if s.kont=0 then ⟨2,0,s.env,0,h⟩
    else match get s.kont 0 with
      | 0 => ⟨0,get s.kont 1,get s.kont 2,n+1,
          node 1 (get s.env 0) 0 (get s.kont 3)::h⟩
      | 1 => ⟨1,0,n+1,get s.kont 3,node (get s.kont 1) s.env 0 0::h⟩
      | 2 => ⟨0,get s.kont 1,s.env,get s.kont 3,h⟩
      | 3 => if get s.env 0=0 then ⟨1,0,get s.env 1,get s.kont 3,h⟩
          else ⟨0,get s.kont 1,get s.env 1,get s.kont 3,h⟩
      | _ => ⟨2,0,s.env,0,h⟩
  else s

inductive Action where
  | put (regs : List Expr)
  | test (e : Expr) (yes no : Action)

def Action.eval : Action → List ℕ → List ℕ
  | .put es,v => es.map (fun e=>e.eval v)++v.drop 5
  | .test e yes no,v => if e.eval v=0 then yes.eval v else no.eval v

noncomputable def expressionList (es : List Expr) :
    PolyProgram (fun v=>es.map (fun e=>e.eval v)++v.drop 5) :=
  match es with
  | [] => (PolyProgram.drop 5).ofEq (fun _=>rfl)
  | e::es => (e.program.cons (expressionList es)).ofEq (fun _=>rfl)

noncomputable def Action.program : (a : Action) → PolyProgram a.eval
  | .put es => expressionList es
  | .test e yes no => (PolyProgram.branch e.program yes.program no.program).ofEq (by
      intro v
      simp only [Action.eval,List.headI_cons]
      rfl)

abbrev r (i : ℕ) : Expr := .reg i
abbrev c (i : ℕ) : Expr := .const i
abbrev g (addr : Expr) (field : Fin 4) : Expr := readExpr 5 4 addr field
abbrev n : Expr := .reg 4
abbrev fresh : Expr := .add n (c 1)

def put (md pc env kont : Expr) : Action := .put [md,pc,env,kont,n]
def alloc (md pc env kont a b d e : Expr) : Action :=
  .put [md,pc,env,kont,fresh,a,b,d,e]

def halt : Action := put (c 2) (c 0) (r 2) (c 0)

def evalZero : Action := alloc (c 1) (c 0) fresh (r 3) (c 0) (r 2) (c 0) (c 0)
def evalSucc : Action := alloc (c 1) (c 0) fresh (r 3) (.add (g (r 2) 0) (c 1)) (c 0) (c 0) (c 0)
def evalTail : Action := put (c 1) (c 0) (g (r 2) 1) (r 3)
def evalCons : Action := alloc (c 0) (g (r 1) 1) (r 2) fresh (c 0) (g (r 1) 2) (r 2) (r 3)
def evalComp : Action := alloc (c 0) (g (r 1) 2) (r 2) fresh (c 2) (g (r 1) 1) (c 0) (r 3)
def evalCase : Action := .test (g (r 2) 0)
  (put (c 0) (g (r 1) 1) (g (r 2) 1) (r 3))
  (alloc (c 0) (g (r 1) 2) fresh (r 3) (.sub (g (r 2) 0) (c 1)) (g (r 2) 1) (c 0) (c 0))
def evalFix : Action := alloc (c 0) (g (r 1) 1) (r 2) fresh (c 3) (r 1) (c 0) (r 3)

def switch (e : Expr) : ℕ → List Action → Action
  | _,[] => halt
  | j,a::as => .test (.eq e (c j)) (switch e (j+1) as) a

def evalAction : Action := switch (g (r 1) 0) 0
  [evalZero,evalSucc,evalTail,evalCons,evalComp,evalCase,evalFix]

def retCons1 : Action := alloc (c 0) (g (r 3) 1) (g (r 3) 2) fresh
  (c 1) (g (r 2) 0) (c 0) (g (r 3) 3)
def retCons2 : Action := alloc (c 1) (c 0) fresh (g (r 3) 3)
  (g (r 3) 1) (r 2) (c 0) (c 0)
def retComp : Action := put (c 0) (g (r 3) 1) (r 2) (g (r 3) 3)
def retFix : Action := .test (g (r 2) 0)
  (put (c 1) (c 0) (g (r 2) 1) (g (r 3) 3))
  (put (c 0) (g (r 3) 1) (g (r 2) 1) (g (r 3) 3))
def returnAction : Action := .test (r 3) halt
  (switch (g (r 3) 0) 0 [retCons1,retCons2,retComp,retFix])

def tickAction : Action := .test (r 0) evalAction
  (.test (.eq (r 0) (c 1)) (put (r 0) (r 1) (r 2) (r 3)) returnAction)

def rawTick : List ℕ → List ℕ := tickAction.eval
noncomputable def tickProgram : PolyProgram rawTick := tickAction.program

lemma expr_reg_encode (s : State) (i : Fin 5) :
    (r i.val).eval s.encode=(![s.mode,s.pc,s.env,s.kont,s.heap.length] : Fin 5 → ℕ) i := by
  fin_cases i <;> rfl

lemma expr_read_encode (s : State) (addr : Expr) (j : Fin 4) :
    (g addr j).eval s.encode=read s.heap (addr.eval s.encode) j := by
  exact readExpr_eval [s.mode,s.pc,s.env,s.kont,s.heap.length] 4 s.heap addr j rfl

lemma put_encode (s : State) (md pc env kont : Expr) :
    (put md pc env kont).eval s.encode=
      (State.mk (md.eval s.encode) (pc.eval s.encode) (env.eval s.encode) (kont.eval s.encode) s.heap).encode := by
  simp only [put,Action.eval,List.map_cons,List.map_nil,State.encode,Expr.eval]
  rfl

lemma alloc_encode (s : State) (md pc env kont a b d e : Expr) :
    (alloc md pc env kont a b d e).eval s.encode=
      (State.mk (md.eval s.encode) (pc.eval s.encode) (env.eval s.encode) (kont.eval s.encode)
        (node (a.eval s.encode) (b.eval s.encode) (d.eval s.encode) (e.eval s.encode)::s.heap)).encode := by
  simp only [alloc,Action.eval,List.map_cons,List.map_nil,State.encode,words_cons,List.length_cons,
    Expr.eval,node,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  rfl

@[simp] lemma encode_head (s : State) : s.encode.headI=s.mode := rfl
@[simp] lemma encode_tail_head (s : State) : s.encode.tail.headI=s.pc := rfl
@[simp] lemma encode_reg0 (s : State) : (s.encode.drop 0).headI=s.mode := rfl
@[simp] lemma encode_reg1 (s : State) : (s.encode.drop 1).headI=s.pc := rfl
@[simp] lemma encode_reg2 (s : State) : (s.encode.drop 2).headI=s.env := rfl
@[simp] lemma encode_reg3 (s : State) : (s.encode.drop 3).headI=s.kont := rfl
@[simp] lemma encode_reg4 (s : State) : (s.encode.drop 4).headI=s.heap.length := rfl

lemma rawTick_encode (s : State) : rawTick s.encode=s.tick.encode := by
  simp only [rawTick,tickAction,Action.eval,Expr.eval]
  change (if s.mode=0 then _ else if (if s.mode=1 then 1 else 0)=0 then _ else _)=_
  by_cases hm : s.mode=0
  · simp only [hm,ite_true,State.tick]
    generalize he : read s.heap s.pc 0=a
    rcases Nat.lt_or_ge a 7 with ha | ha
    · interval_cases a <;> simp [evalAction,switch,Action.eval,Expr.eval,expr_read_encode,
      he,put_encode,alloc_encode,evalZero,evalSucc,evalTail,evalCons,
      evalComp,evalCase,evalFix,halt]
      all_goals split_ifs <;> rfl
    · obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le ha
      rw [hb, Nat.add_comm 7 b] at he ⊢
      simp [evalAction,switch,Action.eval,Expr.eval,expr_read_encode,he,put_encode,halt]
  · by_cases hm1 : s.mode=1
    · simp only [hm1,ite_true,State.tick]
      by_cases hk : s.kont=0
      · simp [returnAction,Action.eval,Expr.eval,hk,halt,put_encode, -List.drop_one]
      · simp only [returnAction,Action.eval,Expr.eval]
        change (if s.kont=0 then _ else _)=_
        simp only [hk,ite_false]
        generalize he : read s.heap s.kont 0=a
        rcases Nat.lt_or_ge a 4 with ha | ha
        · interval_cases a <;> simp [switch,Action.eval,Expr.eval,expr_read_encode,
          he,put_encode,alloc_encode,retCons1,retCons2,retComp,retFix,halt]
          all_goals split_ifs <;> rfl
        · obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le ha
          rw [hb,Nat.add_comm 4 b] at he ⊢
          simp [switch,Action.eval,Expr.eval,expr_read_encode,he,put_encode,halt]
    · simp [hm,hm1,State.tick,put_encode,Expr.eval]

def maximum (v : List ℕ) : ℕ := v.foldr max 0
@[simp] lemma maximum_nil : maximum []=0 := rfl
@[simp] lemma maximum_cons (a : ℕ) (v : List ℕ) : maximum (a::v)=max a (maximum v) := rfl

lemma maximum_append (v w : List ℕ) : maximum (v++w)=max (maximum v) (maximum w) := by
  induction v with
  | nil => simp
  | cons a v ih => simp only [List.cons_append,maximum_cons,ih,max_assoc]

lemma maximum_drop (v : List ℕ) (n : ℕ) : maximum (v.drop n)≤ maximum v := by
  induction n generalizing v with
  | zero => exact le_rfl
  | succ n ih =>
    cases v with
    | nil => simp
    | cons a v => exact (ih v).trans (le_max_right _ _)

lemma head_le_maximum (v : List ℕ) : v.headI≤ maximum v := by
  cases v with
  | nil => rfl
  | cons a v => exact le_max_left _ _

lemma maximum_le_magnitude (v : List ℕ) : maximum v≤ magnitude v := by
  induction v with
  | nil => rfl
  | cons a v ih => simp only [maximum_cons,magnitude_cons]; omega

lemma length_le_magnitude (v : List ℕ) : v.length≤ magnitude v := by
  induction v with
  | nil => rfl
  | cons a v ih => simp only [List.length_cons,magnitude_cons]; omega

lemma magnitude_le_length_maximum (v : List ℕ) : magnitude v≤v.length*(maximum v+1) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    simp only [magnitude_cons,List.length_cons,maximum_cons]
    have ha : a≤ max a (maximum v) := le_max_left _ _
    have hh : maximum v≤ max a (maximum v) := le_max_right _ _
    have hi := Nat.mul_le_mul_left v.length (Nat.add_le_add_right hh 1)
    nlinarith

lemma reg_le_maximum (v : List ℕ) (i : ℕ) : (r i).eval v≤ maximum v :=
  (head_le_maximum (v.drop i)).trans (maximum_drop v i)

lemma get_le_maximum (v : List ℕ) (a : Expr) (j : Fin 4) :
    (g a j).eval v≤ maximum v := by
  by_cases hz : a.eval v=0
  · simp only [g,readExpr,Expr.eval,hz,ite_true,show (1:ℕ)≠0 by omega,ite_false]
    exact Nat.zero_le _
  · simp only [g,readExpr,Expr.eval,hz,ite_false,ite_true]
    exact (head_le_maximum _).trans (maximum_drop v _)

def Small (e : Expr) : Prop := ∀v,e.eval v≤ maximum v+3
lemma small_reg (i : ℕ) : Small (r i) := fun v=>(reg_le_maximum v i).trans (by omega)
lemma small_get (a : Expr) (j : Fin 4) : Small (g a j) := fun v=>(get_le_maximum v a j).trans (by omega)
lemma small_const (i : ℕ) (hi : i≤3) : Small (c i) := fun v=>by change i≤_; omega
lemma small_fresh : Small fresh := fun v=>by
  have h := reg_le_maximum v 4
  change (r 4).eval v+1≤_
  omega
lemma small_succ_get (a : Expr) (j : Fin 4) : Small (.add (g a j) (c 1)) := fun v=>by
  have h := get_le_maximum v a j
  change (g a j).eval v+1≤_
  omega
lemma small_pred_get (a : Expr) (j : Fin 4) : Small (.sub (g a j) (c 1)) := fun v=>by
  have h := get_le_maximum v a j
  change (g a j).eval v-1≤_
  omega

def Action.Safe (a : Action) : Prop := ∀v,
    (a.eval v).length≤v.length+9 ∧ maximum (a.eval v)≤ maximum v+3

lemma maximum_map_small (es : List Expr) (hs : ∀e∈es,Small e) (v : List ℕ) :
    maximum (es.map (fun e=>e.eval v))≤ maximum v+3 := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons,maximum_cons]
    exact max_le (hs e (by simp) v) (ih (fun f hf=>hs f (by simp [hf])))

lemma Action.Safe.put {es : List Expr} (hl : es.length≤9) (hs : ∀e∈es,Small e) :
    Action.Safe (.put es) := by
  intro v
  constructor
  · simp only [Action.eval,List.length_append,List.length_map,List.length_drop]
    omega
  · simp only [Action.eval,maximum_append]
    exact max_le (maximum_map_small es hs v) ((maximum_drop v 5).trans (by omega))

lemma Action.Safe.test {e a b} (ha : Action.Safe a) (hb : Action.Safe b) :
    Action.Safe (.test e a b) := by
  intro v
  simp only [Action.eval]
  split_ifs <;> [exact ha v; exact hb v]

lemma safe_put {md pc env kont : Expr} (hm : Small md) (hp : Small pc) (he : Small env) (hk : Small kont) :
    Action.Safe (put md pc env kont) := by
  apply Action.Safe.put (by simp)
  intro e he'
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he'
  rcases he' with rfl|rfl|rfl|rfl|rfl
  · exact hm
  · exact hp
  · exact he
  · exact hk
  · exact small_reg 4

lemma safe_alloc {md pc env kont a b d e : Expr}
    (hm : Small md) (hp : Small pc) (he : Small env) (hk : Small kont)
    (ha : Small a) (hb : Small b) (hd : Small d) (he' : Small e) :
    Action.Safe (alloc md pc env kont a b d e) := by
  apply Action.Safe.put (by simp)
  intro f hf
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact hm
  · exact hp
  · exact he
  · exact hk
  · exact small_fresh
  · exact ha
  · exact hb
  · exact hd
  · exact he'

lemma safe_halt : Action.Safe halt :=
  safe_put (small_const 2 (by omega)) (small_const 0 (by omega)) (small_reg 2) (small_const 0 (by omega))

lemma safe_switch (e : Expr) (j : ℕ) (as : List Action) (hs : ∀a∈as,Action.Safe a) :
    Action.Safe (switch e j as) := by
  induction as generalizing j with
  | nil => exact safe_halt
  | cons a as ih =>
    exact Action.Safe.test (ih (j+1) (fun b hb=>hs b (by simp [hb]))) (hs a (by simp))

lemma safe_evalAction : Action.Safe evalAction := by
  apply safe_switch
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [evalZero,evalSucc,evalTail,evalCons,evalComp,evalCase,evalFix]
  all_goals first | apply Action.Safe.test | skip
  all_goals first | apply safe_alloc | apply safe_put
  all_goals first | exact small_reg _ | exact small_get _ _ | exact small_fresh |
    exact small_succ_get _ _ | exact small_pred_get _ _ | exact small_const _ (by omega)

lemma safe_returnAction : Action.Safe returnAction := by
  apply Action.Safe.test safe_halt
  apply safe_switch
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl
  all_goals simp only [retCons1,retCons2,retComp,retFix]
  all_goals first | apply Action.Safe.test | skip
  all_goals first | apply safe_alloc | apply safe_put
  all_goals first | exact small_reg _ | exact small_get _ _ | exact small_fresh | exact small_const _ (by omega)

lemma rawTick_safe (v : List ℕ) :
    (rawTick v).length≤v.length+9 ∧ maximum (rawTick v)≤ maximum v+3 := by
  apply Action.Safe.test safe_evalAction (Action.Safe.test ?_ safe_returnAction) v
  exact safe_put (small_reg 0) (small_reg 1) (small_reg 2) (small_reg 3)

lemma rawTick_iter_bounds (v : List ℕ) (i : ℕ) :
    (rawTick^[i] v).length≤v.length+9*i ∧ maximum (rawTick^[i] v)≤ maximum v+3*i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have hh := rawTick_safe (rawTick^[i] v)
    constructor <;> omega

lemma rawTick_iter_magnitude (n : ℕ) (v : List ℕ) (i : ℕ) (hi : i≤n) :
    magnitude (rawTick^[i] v)≤100*(magnitude (n::v)+1)^2 := by
  have hb := rawTick_iter_bounds v i
  have hl := length_le_magnitude v
  have hm := maximum_le_magnitude v
  have hs := magnitude_le_length_maximum (rawTick^[i] v)
  have h1 : (rawTick^[i] v).length≤10*(magnitude (n::v)+1) := by
    simp only [magnitude_cons]; omega
  have h2 : maximum (rawTick^[i] v)+1≤10*(magnitude (n::v)+1) := by
    simp only [magnitude_cons]; omega
  have h := Nat.mul_le_mul h1 h2
  nlinarith

noncomputable def boundedInterpreter : PolyProgram (fun v=>rawTick^[v.headI] v.tail) :=
  PolyProgram.iterate tickProgram (Polynomial.C 100*(Polynomial.X+1)^2) (by
    intro n v i hi
    simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using rawTick_iter_magnitude n v i hi)

end MinUncut.Costed.Arena

end OAI
