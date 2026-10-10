import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.RegisterProc

namespace OAI

namespace MatchingFPRAS.FiniteStore
open Turing MachineCost RegisterProc

variable {K Λ σ : Type} [DecidableEq K]

def stmt : TM2.Stmt (fun _ : K=>Bool) Λ σ → σ →
    TM2.Stmt (fun _ : K=>Bool) (Λ×σ) (Option Bool)
  | .push k f q,v => .push k (fun _=>f v) (stmt q v)
  | .peek k f q,v => .peek k (fun _ x=>x)
      (.branch Option.isNone (stmt q (f v none))
        (.branch (fun x=>x.getD false) (stmt q (f v (some true))) (stmt q (f v (some false)))))
  | .pop k f q,v => .pop k (fun _ x=>x)
      (.branch Option.isNone (stmt q (f v none))
        (.branch (fun x=>x.getD false) (stmt q (f v (some true))) (stmt q (f v (some false)))))
  | .load f q,v => stmt q (f v)
  | .branch f q r,v => if f v then stmt q v else stmt r v
  | .goto f,v => .load (fun _=>none) (.goto (fun _=>(f v,v)))
  | .halt,_ => .load (fun _=>none) .halt

def cfg (c : TM2.Cfg (fun _ : K=>Bool) Λ σ) :
    TM2.Cfg (fun _ : K=>Bool) (Λ×σ) (Option Bool) :=
  ⟨c.l.map (fun l=>(l,c.var)),none,c.stk⟩

theorem stmt_eval (q : TM2.Stmt (fun _ : K=>Bool) Λ σ) (v : σ) (u : Option Bool)
    (S : K→List Bool) : TM2.stepAux (stmt q v) u S=cfg (TM2.stepAux q v S) := by
  induction q generalizing v u S with
  | push k f q ih => simpa only [stmt,TM2.stepAux] using ih v u (Function.update S k (f v::S k))
  | peek k f q ih =>
    cases hh : (S k).head? with
    | none => simpa only [stmt,TM2.stepAux,hh,Option.isNone_none,Bool.cond_true] using ih (f v none) none S
    | some b => cases b <;> simpa only [stmt,TM2.stepAux,hh,Option.isNone_some,Bool.cond_false,
      Option.getD_some,Bool.cond_true] using ih (f v (S k).head?) (S k).head? S
  | pop k f q ih =>
    cases hh : (S k).head? with
    | none => simpa only [stmt,TM2.stepAux,hh,Option.isNone_none,Bool.cond_true] using ih (f v none) none (Function.update S k (S k).tail)
    | some b => cases b <;> simpa only [stmt,TM2.stepAux,hh,Option.isNone_some,Bool.cond_false,
      Option.getD_some,Bool.cond_true] using ih (f v (S k).head?) (S k).head? (Function.update S k (S k).tail)
  | load f q ih => exact ih (f v) u S
  | branch f q r ihq ihr =>
    cases hh : f v with
    | false => simpa only [stmt,TM2.stepAux,hh,Bool.false_eq_true,↓reduceIte,Bool.cond_false] using ihr v u S
    | true => simpa only [stmt,TM2.stepAux,hh,↓reduceIte,Bool.cond_true] using ihq v u S
  | goto f => rfl
  | halt => rfl

def program (M : Λ→TM2.Stmt (fun _ : K=>Bool) Λ σ) :
    Λ×σ→TM2.Stmt (fun _ : K=>Bool) (Λ×σ) (Option Bool) := fun p=>stmt (M p.1) p.2
lemma advance_cfg (M : Λ→TM2.Stmt (fun _ : K=>Bool) Λ σ)
    (c : TM2.Cfg (fun _ : K=>Bool) Λ σ) :
    advance (TM2.step (program M)) (cfg c)=cfg (advance (TM2.step M) c) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l => exact stmt_eval (M l) v none S
lemma run_cfg (M : Λ→TM2.Stmt (fun _ : K=>Bool) Λ σ) (n : ℕ)
    (c : TM2.Cfg (fun _ : K=>Bool) Λ σ) :
    MachineCost.run (TM2.step (program M)) n (cfg c)=cfg (MachineCost.run (TM2.step M) n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [MachineCost.run,advance_cfg,ih,MachineCost.run]

def procedure [Fintype Λ] [DecidableEq Λ] [Inhabited Λ] [Fintype σ] [DecidableEq σ]
    (M : Λ→TM2.Stmt (fun _ : K=>Bool) Λ σ) (v : σ) : Proc K :=
  { Label := Λ×σ
    labels := inferInstance
    entry := ⟨(default,v)⟩
    code := program M }

theorem exec [Fintype Λ] [DecidableEq Λ] [Inhabited Λ] [Fintype σ] [DecidableEq σ]
    (M : Λ→TM2.Stmt (fun _ : K=>Bool) Λ σ) (v w : σ) (A B : Stack K) (n : ℕ)
    (h : MachineCost.run (TM2.step M) n ⟨some default,v,A⟩=⟨none,w,B⟩) :
    Exec (procedure M v) A B n := by
  refine ⟨n,le_rfl,?_⟩
  exact (run_cfg M n ⟨some default,v,A⟩).trans (congrArg cfg h)
end MatchingFPRAS.FiniteStore

end OAI
