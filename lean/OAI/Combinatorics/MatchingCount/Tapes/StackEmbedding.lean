import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.StackCompilerCost

namespace OAI

namespace MatchingFPRAS.StackEmbedding
open Turing MachineCost

variable {K J α Λ σ τ : Type*} [DecidableEq K] [DecidableEq J]
open scoped Classical

noncomputable def extend (e : K ↪ J) (S : K → List α) (R : J → List α) (j : J) : List α :=
  if h : ∃ k,e k=j then S (Classical.choose h) else R j
omit [DecidableEq K] [DecidableEq J] in
@[simp] lemma extend_on (e : K ↪ J) (S : K → List α) (R : J → List α) (k : K) :
    extend e S R (e k)=S k := by
  have h : ∃ l,e l=e k := ⟨k,rfl⟩
  rw [extend,dite_eq_left h,e.injective (Classical.choose_spec h)]
omit [DecidableEq K] [DecidableEq J] in
lemma extend_off (e : K ↪ J) (S : K → List α) (R : J → List α) (j : J)
    (h : ¬∃ k,e k=j) : extend e S R j=R j := by rw [extend,dite_eq_right h]
lemma extend_update (e : K ↪ J) (S : K → List α) (R : J → List α) (k : K) (w : List α) :
    Function.update (extend e S R) (e k) w=extend e (Function.update S k w) R := by
  funext j
  by_cases h : ∃ l,e l=j
  · obtain ⟨l,rfl⟩:=h
    by_cases hl : l=k
    · subst l; simp
    · have hne : e l≠e k := fun h=>hl (e.injective h)
      simp [Function.update_of_ne hne,Function.update_of_ne hl]
  · have hne : j≠e k := fun h'=>h ⟨k,h'.symm⟩
    rw [Function.update_of_ne hne,extend_off e _ _ j h,extend_off e _ _ j h]

def stmt (e : K ↪ J) : TM2.Stmt (fun _ : K=>α) Λ σ → TM2.Stmt (fun _ : J=>α) Λ (σ×τ)
  | .push k a q => .push (e k) (fun v=>a v.1) (stmt e q)
  | .peek k a q => .peek (e k) (fun v x=>(a v.1 x,v.2)) (stmt e q)
  | .pop k a q => .pop (e k) (fun v x=>(a v.1 x,v.2)) (stmt e q)
  | .load a q => .load (fun v=>(a v.1,v.2)) (stmt e q)
  | .branch p q r => .branch (fun v=>p v.1) (stmt e q) (stmt e r)
  | .goto l => .goto (fun v=>l v.1)
  | .halt => .halt
noncomputable def cfg (e : K ↪ J) (R : J → List α) (u : τ)
    (c : TM2.Cfg (fun _ : K=>α) Λ σ) : TM2.Cfg (fun _ : J=>α) Λ (σ×τ) :=
  ⟨c.l,(c.var,u),extend e c.stk R⟩
lemma stmt_eval (e : K ↪ J) (R : J → List α) (u : τ)
    (q : TM2.Stmt (fun _ : K=>α) Λ σ) (v : σ) (S : K → List α) :
    TM2.stepAux (stmt e q) (v,u) (extend e S R)=cfg e R u (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k a q ih => simpa only [stmt,TM2.stepAux,extend_on,extend_update] using ih v (Function.update S k (a v::S k))
  | peek k a q ih => simpa only [stmt,TM2.stepAux,extend_on] using ih (a v (S k).head?) S
  | pop k a q ih => simpa only [stmt,TM2.stepAux,extend_on,extend_update] using ih (a v (S k).head?) (Function.update S k (S k).tail)
  | load a q ih => exact ih (a v) S
  | branch p q r ihq ihr =>
    cases h : p v <;> simp only [stmt,TM2.stepAux,h,Bool.cond_false,Bool.cond_true] <;> first | apply ihr | apply ihq
  | goto l => rfl
  | halt => rfl
omit [DecidableEq K] [DecidableEq J] in
lemma stmt_accesses (e : K ↪ J) (q : TM2.Stmt (fun _ : K=>α) Λ σ) :
    StackCost.accesses (stmt (τ:=τ) e q)=StackCost.accesses q := by
  induction q <;> simp_all [stmt,StackCost.accesses]

def program (e : K ↪ J) (M : Λ → TM2.Stmt (fun _ : K=>α) Λ σ) :=
  fun l=>stmt (τ:=τ) e (M l)
lemma advance_cfg (e : K ↪ J) (M : Λ → TM2.Stmt (fun _ : K=>α) Λ σ)
    (R : J → List α) (u : τ) (c : TM2.Cfg (fun _ : K=>α) Λ σ) :
    advance (TM2.step (program e M)) (cfg e R u c)=cfg e R u (advance (TM2.step M) c) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l => exact stmt_eval e R u (M l) v S

theorem run_cfg (e : K ↪ J) (M : Λ → TM2.Stmt (fun _ : K=>α) Λ σ)
    (R : J → List α) (u : τ) (n : ℕ) (c : TM2.Cfg (fun _ : K=>α) Λ σ) :
    MachineCost.run (TM2.step (program e M)) n (cfg e R u c)=
      cfg e R u (MachineCost.run (TM2.step M) n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [MachineCost.run,advance_cfg,ih,MachineCost.run]
end MatchingFPRAS.StackEmbedding

end OAI
