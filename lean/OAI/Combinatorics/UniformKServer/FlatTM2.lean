import Mathlib
import OAI.Combinatorics.UniformKServer.StackRun

namespace OAI

noncomputable section

/-! Flatten Mathlib's finitely supported TM2 programs into literal single
stack primitives. Every variable type and alphabet in this compiler is finite.
In particular a TM2 expression's arithmetic is not counted as one bit step. -/
namespace UniformKServer.FlatTM2
open Turing StackCompiler
open scoped Classical
variable {K Γ Λ V : Type} [Fintype K] [Fintype Γ] [Fintype V]
  [DecidableEq K] [Inhabited Λ]
variable (M : Λ → TM2.Stmt (fun _ : K=>Γ) Λ V) (S : Finset Λ) (hs : TM2.Supports M S)

abbrev Node := {x : Option (TM2.Stmt (fun _ : K=>Γ) Λ V) // x∈TM2.stmts M S}
abbrev Local := Node M S × V

def nodes : Local M S ≃ Fin (Fintype.card (Local M S)) := Fintype.equivFin _
def keys : K ≃ Fin (Fintype.card K) := Fintype.equivFin _
def letters : Γ ≃ Fin (Fintype.card Γ) := Fintype.equivFin _

def done : Node M S := ⟨none,by simp [TM2.stmts]⟩

def root (l : Λ) (hl : l∈S) : Node M S :=
  ⟨some (M l),Finset.some_mem_insertNone.mpr (Finset.mem_biUnion.mpr
    ⟨l,hl,TM2.stmts₁_self⟩)⟩

def sub {s t : TM2.Stmt (fun _ : K=>Γ) Λ V} (ht : t∈TM2.stmts₁ s)
    (hs : some s∈TM2.stmts M S) : Node M S := ⟨some t,TM2.stmts_trans ht hs⟩

/-- The action is allowed to inspect only stack heads and the finite local
variable. Its maps have finite domain and finite range. -/
def action (x : Local M S) (hds : Fin (Fintype.card K) → Option (Fin (Fintype.card Γ))) :
    Action (Fintype.card (Local M S)) (Fintype.card K) (Fintype.card Γ) :=
  let make (y : Node M S) (v : V) (ops : K → Op (Fintype.card Γ)) :=
    { control:=nodes M S (y,v),inputMove:=HeadMove.stay,
      stackOp:=fun i=>ops (keys.symm i),emit:=none,yield:=y.val.isNone }
  match x.1 with
  | ⟨none,_⟩=>make (done M S) x.2 (fun _=>.keep)
  | ⟨some (.push k f q),h⟩=>make (sub M S (t:=q) (by simp [TM2.stmts₁,TM2.stmts₁_self]) h) x.2
      (fun i=>if i=k then .push (letters (f x.2)) else .keep)
  | ⟨some (.peek k f q),h⟩=>make (sub M S (t:=q) (by simp [TM2.stmts₁,TM2.stmts₁_self]) h)
      (f x.2 ((hds (keys k)).map letters.symm)) (fun _=>.keep)
  | ⟨some (.pop k f q),h⟩=>make (sub M S (t:=q) (by simp [TM2.stmts₁,TM2.stmts₁_self]) h)
      (f x.2 ((hds (keys k)).map letters.symm)) (fun i=>if i=k then .pop else .keep)
  | ⟨some (.load f q),h⟩=>make (sub M S (t:=q) (by simp [TM2.stmts₁,TM2.stmts₁_self]) h) (f x.2) (fun _=>.keep)
  | ⟨some (.branch f q₁ q₂),h⟩=>if f x.2 then
      make (sub M S (t:=q₁) (by simp [TM2.stmts₁,TM2.stmts₁_self]) h) x.2 (fun _=>.keep)
    else make (sub M S (t:=q₂) (by simp [TM2.stmts₁,TM2.stmts₁_self]) h) x.2 (fun _=>.keep)
  | ⟨some (.goto f),h⟩=>make (root M S (f x.2) (TM2.stmts_supportsStmt hs h x.2)) x.2
      (fun _=>.keep)
  | ⟨some .halt,_⟩=>make (done M S) x.2 (fun _=>.keep)

/-- A finitely supported Mathlib TM2 has an actual finite-control processor.
It will be initialized with its input on its designated stack. -/
def processor (v₀ : V) : Processor (Fintype.card (Local M S)) (Fintype.card K) (Fintype.card Γ) where
  start:=nodes M S (root M S default hs.1,v₀)
  transition:=fun c _ h _=>action M S hs ((nodes M S).symm c) h

end UniformKServer.FlatTM2

end

end OAI
