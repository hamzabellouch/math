import Mathlib
import OAI.Combinatorics.UniformKServer.FlatTM2

namespace OAI

noncomputable section

namespace UniformKServer.FlatTM2
open Turing StackCompiler
open scoped Classical
variable {K Γ Λ V : Type} [Fintype K] [Fintype Γ] [Fintype V]
  [DecidableEq K] [Inhabited Λ]
variable (M : Λ → TM2.Stmt (fun _ : K=>Γ) Λ V) (S : Finset Λ) (hs : TM2.Supports M S)

structure Runtime where
  pc : Option (TM2.Stmt (fun _ : K=>Γ) Λ V)
  var : V
  store : K → List Γ

/-- Exactly one primitive; the AST is not evaluated in a unit-cost StackCompiler.step. -/
def advance (x : Runtime (K:=K) (Γ:=Γ) (Λ:=Λ) (V:=V)) : Runtime (K:=K) (Γ:=Γ) (Λ:=Λ) (V:=V) :=
  match x.pc with
  | none=>x
  | some (.push k f q)=>⟨some q,x.var,Function.update x.store k (f x.var::x.store k)⟩
  | some (.peek k f q)=>⟨some q,f x.var (x.store k).head?,x.store⟩
  | some (.pop k f q)=>⟨some q,f x.var (x.store k).head?,Function.update x.store k (x.store k).tail⟩
  | some (.load f q)=>⟨some q,f x.var,x.store⟩
  | some (.branch f q₁ q₂)=>⟨some (if f x.var then q₁ else q₂),x.var,x.store⟩
  | some (.goto f)=>⟨some (M (f x.var)),x.var,x.store⟩
  | some .halt=>⟨none,x.var,x.store⟩

include hs in
omit [Fintype K] [Fintype Γ] [Fintype V] in
theorem advance_supported (x : Runtime (K:=K) (Γ:=Γ) (Λ:=Λ) (V:=V))
    (hx : x.pc∈TM2.stmts M S) : (advance M x).pc∈TM2.stmts M S := by
  rcases x with ⟨pc,v,st⟩
  cases pc with
  | none=>exact hx
  | some q=>
    cases q with
    | push k f q | peek k f q | pop k f q | load f q=>
      exact TM2.stmts_trans (by simp [TM2.stmts₁,TM2.stmts₁_self]) hx
    | branch f q₁ q₂=>
      cases h : f v <;> simp only [advance,h,Bool.false_eq_true,↓reduceIte] <;>
        exact TM2.stmts_trans (by simp [TM2.stmts₁,TM2.stmts₁_self]) hx
    | goto f=>
      exact (root M S (f v) (TM2.stmts_supportsStmt hs hx v)).property
    | halt=>exact (done M S).property

def encode (x : Runtime (K:=K) (Γ:=Γ) (Λ:=Λ) (V:=V)) (hx : x.pc∈TM2.stmts M S) :
    State (Fintype.card (Local M S)) (Fintype.card K) (Fintype.card Γ) :=
  ⟨nodes M S (⟨x.pc,hx⟩,x.var),BitTape.blank,
    fun i=>(x.store (keys.symm i)).map letters,[],x.pc.isNone⟩

omit [DecidableEq K] in
theorem heads (st : K → List Γ) (k : K) :
    (((st (keys.symm (keys k))).map letters).head?).map letters.symm=(st k).head? := by
  simp only [Equiv.symm_apply_apply,List.head?_map,Option.map_map]
  simp

theorem encode_step (v₀ : V) (x : Runtime (K:=K) (Γ:=Γ) (Λ:=Λ) (V:=V))
    (hx : x.pc∈TM2.stmts M S) :
    StackCompiler.step (processor M S hs v₀) (encode M S x hx) false =
      encode M S (advance M x) (advance_supported M S hs x hx) := by
  rcases x with ⟨pc,v,st⟩
  cases pc with
  | none=>rfl
  | some q=>
    cases q with
    | push k f q=>
      simp only [StackCompiler.step,encode,Option.isNone_some,Bool.false_eq_true,↓reduceIte,
        processor,Equiv.symm_apply_apply,action,advance,sub]
      congr 1
      · funext i
        by_cases h : keys.symm i=k
        · simp [h,applyOp]
        · simp [h,applyOp,Function.update_of_ne]
    | pop k f q=>
      simp only [StackCompiler.step,encode,Option.isNone_some,Bool.false_eq_true,↓reduceIte,
        processor,Equiv.symm_apply_apply,action,advance,sub,List.head?_map,Option.map_map,
        Function.comp_def,Equiv.symm_apply_apply,Option.map_id']
      congr 1
      · funext i
        by_cases h : keys.symm i=k
        · simp [h,applyOp,List.map_tail]
        · simp [h,applyOp,Function.update_of_ne]
    | peek k f q=>
      simp [StackCompiler.step,encode,processor,action,advance,applyOp,BitTape.shift,sub]
    | load f q=>
      simp [StackCompiler.step,encode,processor,action,advance,applyOp,BitTape.shift,sub]
    | branch f q₁ q₂=>
      cases h:f v <;> simp [StackCompiler.step,encode,processor,action,advance,h,applyOp,BitTape.shift,sub]
    | goto f=>
      simp [StackCompiler.step,encode,processor,action,advance,applyOp,BitTape.shift,root]
    | halt=>
      simp [StackCompiler.step,encode,processor,action,advance,applyOp,BitTape.shift,done]

end UniformKServer.FlatTM2

end

end OAI
