import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.StackEmbedding

namespace OAI

namespace MatchingFPRAS.StackLens
open Turing MachineCost StackEmbedding

structure Lens (σ τ : Type*) where
  get : τ → σ
  put : τ → σ → τ
  get_put : ∀ v s,get (put v s)=s
  put_get : ∀ v,put v (get v)=v
  put_put : ∀ v s t,put (put v s) t=put v t

def Lens.identity (σ : Type*) : Lens σ σ :=
  ⟨id,fun _ s=>s,fun _ _=>rfl,fun _=>rfl,fun _ _ _=>rfl⟩
def Lens.first (σ τ : Type*) : Lens σ (σ×τ) :=
  ⟨Prod.fst,fun v s=>(s,v.2),fun _ _=>rfl,fun _=>rfl,fun _ _ _=>rfl⟩
def Lens.second (σ τ : Type*) : Lens τ (σ×τ) :=
  ⟨Prod.snd,fun v s=>(v.1,s),fun _ _=>rfl,fun _=>rfl,fun _ _ _=>rfl⟩
variable {K J α Λ σ τ : Type*} [DecidableEq K] [DecidableEq J]

def stmt (e : K ↪ J) (L : Lens σ τ) :
    TM2.Stmt (fun _ : K=>α) Λ σ → TM2.Stmt (fun _ : J=>α) Λ τ
  | .push k a q => .push (e k) (fun v=>a (L.get v)) (stmt e L q)
  | .peek k a q => .peek (e k) (fun v x=>L.put v (a (L.get v) x)) (stmt e L q)
  | .pop k a q => .pop (e k) (fun v x=>L.put v (a (L.get v) x)) (stmt e L q)
  | .load a q => .load (fun v=>L.put v (a (L.get v))) (stmt e L q)
  | .branch p q r => .branch (fun v=>p (L.get v)) (stmt e L q) (stmt e L r)
  | .goto l => .goto (fun v=>l (L.get v))
  | .halt => .halt
noncomputable def cfg (e : K ↪ J) (L : Lens σ τ) (R : J → List α) (u : τ)
    (c : TM2.Cfg (fun _ : K=>α) Λ σ) : TM2.Cfg (fun _ : J=>α) Λ τ :=
  ⟨c.l,L.put u c.var,extend e c.stk R⟩
lemma stmt_eval (e : K ↪ J) (L : Lens σ τ) (R : J → List α) (u : τ)
    (q : TM2.Stmt (fun _ : K=>α) Λ σ) (v : σ) (S : K → List α) :
    TM2.stepAux (stmt e L q) (L.put u v) (extend e S R)=
      cfg e L R u (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k a q ih =>
    simpa only [stmt,TM2.stepAux,L.get_put,extend_on,extend_update] using ih v (Function.update S k (a v::S k))
  | peek k a q ih =>
    simpa only [stmt,TM2.stepAux,L.get_put,L.put_put,extend_on] using ih (a v (S k).head?) S
  | pop k a q ih =>
    simpa only [stmt,TM2.stepAux,L.get_put,L.put_put,extend_on,extend_update] using ih (a v (S k).head?) (Function.update S k (S k).tail)
  | load a q ih => simpa only [stmt,TM2.stepAux,L.get_put,L.put_put] using ih (a v) S
  | branch p q r ihq ihr =>
    cases h : p v <;> simp only [stmt,TM2.stepAux,L.get_put,h,Bool.cond_false,Bool.cond_true] <;>
      first | apply ihr | apply ihq
  | goto l => simp only [stmt,TM2.stepAux,cfg,L.get_put]
  | halt => rfl
omit [DecidableEq K] [DecidableEq J] in
lemma accesses (e : K ↪ J) (L : Lens σ τ) (q : TM2.Stmt (fun _ : K=>α) Λ σ) :
    StackCost.accesses (stmt e L q)=StackCost.accesses q := by
  induction q <;> simp_all [stmt,StackCost.accesses]
def program (e : K ↪ J) (L : Lens σ τ) (M : Λ → TM2.Stmt (fun _ : K=>α) Λ σ) :=
  fun l=>stmt e L (M l)
lemma advance_cfg (e : K ↪ J) (L : Lens σ τ) (M : Λ → TM2.Stmt (fun _ : K=>α) Λ σ)
    (R : J → List α) (u : τ) (c : TM2.Cfg (fun _ : K=>α) Λ σ) :
    advance (TM2.step (program e L M)) (cfg e L R u c)=cfg e L R u (advance (TM2.step M) c) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l => exact stmt_eval e L R u (M l) v S

theorem run_cfg (e : K ↪ J) (L : Lens σ τ) (M : Λ → TM2.Stmt (fun _ : K=>α) Λ σ)
    (R : J → List α) (u : τ) (n : ℕ) (c : TM2.Cfg (fun _ : K=>α) Λ σ) :
    MachineCost.run (TM2.step (program e L M)) n (cfg e L R u c)=
      cfg e L R u (MachineCost.run (TM2.step M) n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [MachineCost.run,advance_cfg,ih,MachineCost.run]
end MatchingFPRAS.StackLens

end OAI
