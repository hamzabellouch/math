import Mathlib
import OAI.Computability.MinUncut.Graphs.GeneratedGraph

namespace OAI

namespace MinUncut.Costed.Arena
open Turing.ToPartrec

lemma simulate_cons {f fs v u w A B} (hf : Simulates f v u A) (hfs : Simulates fs v w B) :
    Simulates (.cons f fs) v (u.headI::w) (A+B+3) := by
  intro h pc env k hc hv
  cases hc with
  | cons hp hb ht hcf hcfs =>
    let frame₁ := node 0 (read h pc 2) env k
    let h₁ := frame₁::h
    obtain ⟨h₂,out,n,hn,he,ho,tr⟩ := hf h₁ (read h pc 1) env (h.length+1)
      (hcf.extend frame₁) (hv.extend frame₁)
    have hh : Extends h h₂ := (Extends.cons h frame₁).trans he
    have hr (j : Fin 4) : read h₂ (h.length+1) j=frame₁ j := by
      rw [he.read _ (by simp [h₁]),read_new]
    have start : Trace ⟨0,pc,env,k,h⟩ ⟨0,read h pc 1,env,h.length+1,h₁⟩ 1 := by
      apply Trace.one
      simp only [State.tick,ht,ite_true,h₁,frame₁]
    let frame₂ := node 1 u.headI 0 k
    let h₃ := frame₂::h₂
    have hh₃ : Extends h h₃ := hh.trans (Extends.cons h₂ frame₂)
    have next : Trace ⟨1,0,out,h.length+1,h₂⟩ ⟨0,read h pc 2,env,h₂.length+1,h₃⟩ 1 := by
      apply Trace.one
      simp only [State.tick,show (1:ℕ)≠0 by omega,ite_false,ite_true,
        show h.length+1≠0 by omega,hr,frame₁,node_zero,node_one,node_two,node_three,
        ho.head,h₃,frame₂]
    obtain ⟨h₄,out',m,hm,he',ho',tr'⟩ := hfs h₃ (read h pc 2) env (h₂.length+1)
      (hcfs.mono hh₃) (hv.mono hh₃)
    have hr' (j : Fin 4) : read h₄ (h₂.length+1) j=frame₂ j := by
      rw [he'.read _ (by simp [h₃]),read_new]
    let h₅ := node u.headI out' 0 0::h₄
    have finish : Trace ⟨1,0,out',h₂.length+1,h₄⟩ ⟨1,0,h₄.length+1,k,h₅⟩ 1 := by
      apply Trace.one
      simp only [State.tick,show (1:ℕ)≠0 by omega,ite_false,ite_true,
        show h₂.length+1≠0 by omega,hr',frame₂,node_zero,node_one,node_three,h₅]
    refine ⟨h₅,h₄.length+1,1+n+1+m+1,by omega,
      hh₃.trans (he'.trans (Extends.cons h₄ _)),ho'.push _,?_⟩
    exact (((start.trans tr).trans next).trans tr').trans finish

lemma simulate_fixDone {f v u A} (hf : Simulates f v u A) (hz : u.headI=0) :
    Simulates (.fix f) v u.tail (A+2) := by
  intro h pc env k hc hv
  cases hc with
  | fix hp hb ht hcf =>
    let frame := node 3 pc 0 k
    let h₁ := frame::h
    obtain ⟨h₂,out,n,hn,he,ho,tr⟩ := hf h₁ (read h pc 1) env (h.length+1)
      (hcf.extend frame) (hv.extend frame)
    have hh : Extends h h₂ := (Extends.cons h frame).trans he
    have hr (j : Fin 4) : read h₂ (h.length+1) j=frame j := by
      rw [he.read _ (by simp [h₁]),read_new]
    have start : Trace ⟨0,pc,env,k,h⟩ ⟨0,read h pc 1,env,h.length+1,h₁⟩ 1 := by
      apply Trace.one
      simp only [State.tick,ht,ite_true,h₁,frame]
    have finish : Trace ⟨1,0,out,h.length+1,h₂⟩ ⟨1,0,read h₂ out 1,k,h₂⟩ 1 := by
      apply Trace.one
      simp only [State.tick,show (1:ℕ)≠0 by omega,ite_false,ite_true,
        show h.length+1≠0 by omega,hr,frame,node_zero,node_three,ho.head,hz]
    exact ⟨h₂,read h₂ out 1,1+n+1,by omega,hh,ho.tail,(start.trans tr).trans finish⟩

lemma simulate_fixMore {f v u a w A B} (hf : Simulates f v ((a+1)::u) A)
    (hfix : Simulates (.fix f) u w B) : Simulates (.fix f) v w (A+B+2) := by
  intro h pc env k hc hv
  have hc₀ := hc
  cases hc with
  | fix hp hb ht hcf =>
    let frame := node 3 pc 0 k
    let h₁ := frame::h
    obtain ⟨h₂,out,n,hn,he,ho,tr⟩ := hf h₁ (read h pc 1) env (h.length+1)
      (hcf.extend frame) (hv.extend frame)
    have hh : Extends h h₂ := (Extends.cons h frame).trans he
    have hr (j : Fin 4) : read h₂ (h.length+1) j=frame j := by
      rw [he.read _ (by simp [h₁]),read_new]
    have start : Trace ⟨0,pc,env,k,h⟩ ⟨0,read h pc 1,env,h.length+1,h₁⟩ 1 := by
      apply Trace.one
      simp only [State.tick,ht,ite_true,h₁,frame]
    have next : Trace ⟨1,0,out,h.length+1,h₂⟩ ⟨0,pc,read h₂ out 1,k,h₂⟩ 1 := by
      apply Trace.one
      simp only [State.tick,show (1:ℕ)≠0 by omega,ite_false,ite_true,
        show h.length+1≠0 by omega,hr,frame,node_zero,node_one,node_three,ho.head,
        List.headI_cons,show a+1≠0 by omega]
    obtain ⟨h₃,out',m,hm,he',ho',tr'⟩ := hfix h₂ pc (read h₂ out 1) k (hc₀.mono hh) ho.tail
    exact ⟨h₃,out',1+n+1+m,by omega,hh.trans he',ho',((start.trans tr).trans next).trans tr'⟩

lemma Simulates.mono {c v w A B} (h : Simulates c v w A) (hAB : A≤B) : Simulates c v w B := by
  intro heap pc env k hc hv
  obtain ⟨h',out,n,hn,he,ho,tr⟩ := h heap pc env k hc hv
  exact ⟨h',out,n,hn.trans hAB,he,ho,tr⟩

lemma CodeRun.simulates {c v w t} (h : CodeRun c v w t) : Simulates c v w (3*t) := by
  induction h with
  | zero v => exact (simulate_zero v).mono (by omega)
  | succ v => exact (simulate_succ v).mono (by omega)
  | tail v => exact (simulate_tail v).mono (by omega)
  | cons _ _ ih ih' => exact (simulate_cons ih ih').mono (by omega)
  | comp _ _ ih ih' => exact (simulate_comp ih ih').mono (by omega)
  | caseZero hz _ ih => exact (simulate_caseZero hz ih).mono (by omega)
  | caseSucc _ ih => exact (simulate_caseSucc ih).mono (by omega)
  | fixDone _ hz ih => exact (simulate_fixDone ih hz).mono (by omega)
  | fixMore _ _ ih ih' => exact (simulate_fixMore ih ih').mono (by omega)

open Turing.ToPartrec

def listCells : List ℕ → Heap → ℕ × Heap
  | [],h => (0,h)
  | a::v,h =>
    let r := listCells v h
    (r.2.length+1,node a r.1 0 0::r.2)

lemma listCells_spec (v : List ℕ) (h : Heap) :
    Extends h (listCells v h).2 ∧ ListRep (listCells v h).2 (listCells v h).1 v := by
  induction v with
  | nil => exact ⟨Extends.refl h,ListRep.nil⟩
  | cons a v ih =>
    exact ⟨ih.1.trans (Extends.cons _ _),ih.2.push a⟩

lemma listCells_length (v : List ℕ) (h : Heap) : (listCells v h).2.length=v.length+h.length := by
  induction v with
  | nil => simp [listCells]
  | cons a v ih => simp only [listCells,List.length_cons,ih]; omega

def initialState (c : Code) (v : List ℕ) (base : Heap := []) : State :=
  let hc := codeCells c base.length++base
  let r := listCells v hc
  ⟨0,base.length+(codeCells c base.length).length,r.1,0,r.2⟩

lemma initialState_spec (c : Code) (v : List ℕ) (base : Heap) :
    CodeAt (initialState c v base).heap (initialState c v base).pc c ∧
    ListRep (initialState c v base).heap (initialState c v base).env v := by
  exact ⟨(codeCells_spec c base).mono (listCells_spec v _).1,(listCells_spec v _).2⟩

lemma State.tick_halted (pc env k : ℕ) (h : Heap) :
    (State.mk 2 pc env k h).tick=State.mk 2 pc env k h := by
  simp [State.tick]

lemma Trace.pad_halted {s : State} (env : ℕ) (h : Heap) {n B : ℕ}
    (ht : Trace s ⟨2,0,env,0,h⟩ n) (hn : n≤B) : Trace s ⟨2,0,env,0,h⟩ B := by
  have hs : ∀i,State.tick^[i] (State.mk 2 0 env 0 h)=State.mk 2 0 env 0 h := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply',ih,State.tick_halted]
  have hh := ht.trans (show Trace (State.mk 2 0 env 0 h) _ (B-n) from hs (B-n))
  simpa only [Nat.add_sub_of_le hn] using hh

lemma CodeRun.interpreted {c v w t} (hr : CodeRun c v w t) (base : Heap) {B : ℕ} (hB : t≤B) :
    ∃h out,ListRep h out w ∧
      rawTick^[3*B+1] (initialState c v base).encode=(State.mk 2 0 out 0 h).encode := by
  have hi := initialState_spec c v base
  obtain ⟨h,out,n,hn,he,ho,tr⟩ := CodeRun.simulates hr _ _ _ 0 hi.1 hi.2
  have last : Trace (State.mk 1 0 out 0 h) (State.mk 2 0 out 0 h) 1 := by
    apply Trace.one
    simp [State.tick]
  have tr' := (tr.trans last).pad_halted out h (by omega : n+1≤3*B+1)
  refine ⟨h,out,ho,?_⟩
  have interp (s : State) (i : ℕ) : rawTick^[i] s.encode=(State.tick^[i] s).encode := by
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply',ih,rawTick_encode,Function.iterate_succ_apply']
  rw [interp]
  exact congrArg State.encode tr'

structure OutputState where
  ptr : ℕ
  heap : Heap
  acc : List ℕ

def OutputState.encode (s : OutputState) : List ℕ :=
  [s.ptr,s.heap.length,s.acc.length]++s.acc++2::words s.heap

def OutputState.tick (s : OutputState) : OutputState :=
  if s.ptr=0 then s else ⟨read s.heap s.ptr 1,s.heap,read s.heap s.ptr 0::s.acc⟩

def outRead (j : Fin 4) : Expr :=
  .at (.add (.add (.const (4+j.val)) (.reg 2))
    (.mul (.const 4) (.sub (.reg 1) (.reg 0))))

def outputStep (v : List ℕ) : List ℕ :=
  if v.headI=0 then v else
    [(outRead 1).eval v,(r 1).eval v,(r 2).eval v+1,(outRead 0).eval v]++v.drop 3

noncomputable def outputStepProgram : PolyProgram outputStep := by
  let P := (outRead 1).program.cons ((r 1).program.cons
    ((Expr.add (r 2) (c 1)).program.cons ((outRead 0).program.cons (PolyProgram.drop 3))))
  exact (PolyProgram.branch PolyProgram.head PolyProgram.id P).ofEq (by
    intro v
    rfl)

@[simp] lemma out_encode_reg0 (s : OutputState) : (r 0).eval s.encode=s.ptr := rfl
@[simp] lemma out_encode_reg1 (s : OutputState) : (r 1).eval s.encode=s.heap.length := rfl
@[simp] lemma out_encode_reg2 (s : OutputState) : (r 2).eval s.encode=s.acc.length := rfl

lemma outRead_encode (s : OutputState) (j : Fin 4) (hp : s.ptr≠0) :
    (outRead j).eval s.encode=read s.heap s.ptr j := by
  rw [read_words,ite_eq_right hp]
  simp only [outRead,Expr.eval]
  change (s.encode.drop (4+j.val+s.acc.length+4*(s.heap.length-s.ptr))).headI=_
  rw [show 4+j.val+s.acc.length+4*(s.heap.length-s.ptr)=
    (3+s.acc.length+1)+(4*(s.heap.length-s.ptr)+j.val) by omega,←List.drop_drop]
  have hs : s.encode.drop (3+s.acc.length+1)=words s.heap := by
    have he : ([s.ptr,s.heap.length,s.acc.length]++s.acc++[2]).length=3+s.acc.length+1 := by simp; omega
    have hh : (([s.ptr,s.heap.length,s.acc.length]++s.acc++[2])++words s.heap).drop
        ([s.ptr,s.heap.length,s.acc.length]++s.acc++[2]).length=words s.heap := List.drop_left
    rw [he] at hh
    simpa only [OutputState.encode,List.append_assoc,List.singleton_append] using hh
  rw [hs]

lemma outputStep_encode (s : OutputState) : outputStep s.encode=s.tick.encode := by
  by_cases hp : s.ptr=0
  · simp only [outputStep,OutputState.tick,hp,OutputState.encode,List.cons_append,
      List.nil_append,List.headI_cons,ite_true]
  · simp only [outputStep,OutputState.tick,hp,ite_false]
    change (if s.ptr=0 then _ else _) = _
    rw [ite_eq_right hp,outRead_encode s 1 hp,outRead_encode s 0 hp,out_encode_reg1,out_encode_reg2]
    rfl

lemma output_raw_iter (s : OutputState) (i : ℕ) :
    outputStep^[i] s.encode=(OutputState.tick^[i] s).encode := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply',ih,outputStep_encode,Function.iterate_succ_apply']

lemma ListRep.output_iter {h p v} (hv : ListRep h p v) (acc : List ℕ) :
    OutputState.tick^[v.length] ⟨p,h,acc⟩=⟨0,h,v.reverse++acc⟩ := by
  induction hv generalizing acc with
  | nil => rfl
  | @cons p a q v hpos hb ha hq hv ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    have hs : OutputState.tick ⟨p,h,acc⟩=⟨q,h,a::acc⟩ := by
      simp only [OutputState.tick,show ¬(_=0) from Nat.ne_of_gt hpos,ite_false,ha,hq]
    rw [hs,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

lemma output_null_iter (h : Heap) (acc : List ℕ) (i : ℕ) :
    OutputState.tick^[i] ⟨0,h,acc⟩=⟨0,h,acc⟩ := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply',ih]; rfl

lemma ListRep.output_padded {h p v} (hv : ListRep h p v) (acc : List ℕ) {B : ℕ} (hB : v.length≤B) :
    outputStep^[B] (OutputState.mk p h acc).encode=(OutputState.mk 0 h (v.reverse++acc)).encode := by
  rw [output_raw_iter,show B=(B-v.length)+v.length by omega,Function.iterate_add_apply,
    hv.output_iter,output_null_iter]

end MinUncut.Costed.Arena

end OAI
