import Mathlib
import OAI.Combinatorics.UniformKServer.FlatOperational

namespace OAI

noncomputable section

namespace UniformKServer.FlatTM2
open Turing StackCompiler
open scoped Classical
variable {K Γ Λ V : Type} [Fintype K] [Fintype Γ] [Fintype V]
  [DecidableEq K] [Inhabited Λ]
variable (M : Λ → TM2.Stmt (fun _ : K=>Γ) Λ V) (S : Finset Λ) (hs : TM2.Supports M S)

def fromCfg (c : TM2.Cfg (fun _ : K=>Γ) Λ V) : Runtime (K:=K) (Γ:=Γ) (Λ:=Λ) (V:=V) :=
  ⟨c.l.map M,c.var,c.stk⟩

omit [Fintype K] [Fintype Γ] [Fintype V] [Inhabited Λ] in
/-- Every Mathlib TM2 macro-step is a finite sequence of literal primitives. -/
theorem advances_aux (q : TM2.Stmt (fun _ : K=>Γ) Λ V) (v : V) (st : K → List Γ) :
    ∃t : ℕ,(advance M)^[t] ⟨some q,v,st⟩=fromCfg M (TM2.stepAux q v st) := by
  induction q generalizing v st with
  | push k f q ih=>
    obtain ⟨t,ht⟩:=ih v (Function.update st k (f v::st k))
    exact ⟨t+1,by simpa [Function.iterate_succ_apply,advance] using ht⟩
  | peek k f q ih=>
    obtain ⟨t,ht⟩:=ih (f v (st k).head?) st
    exact ⟨t+1,by simpa [Function.iterate_succ_apply,advance] using ht⟩
  | pop k f q ih=>
    obtain ⟨t,ht⟩:=ih (f v (st k).head?) (Function.update st k (st k).tail)
    exact ⟨t+1,by simpa [Function.iterate_succ_apply,advance] using ht⟩
  | load f q ih=>
    obtain ⟨t,ht⟩:=ih (f v) st
    exact ⟨t+1,by simpa [Function.iterate_succ_apply,advance] using ht⟩
  | branch f q₁ q₂ ih₁ ih₂=>
    cases h:f v with
    | false=>
      obtain ⟨t,ht⟩:=ih₂ v st
      exact ⟨t+1,by simpa [Function.iterate_succ_apply,advance,h] using ht⟩
    | true=>
      obtain ⟨t,ht⟩:=ih₁ v st
      exact ⟨t+1,by simpa [Function.iterate_succ_apply,advance,h] using ht⟩
  | goto f=>exact ⟨1,rfl⟩
  | halt=>exact ⟨1,rfl⟩

omit [Fintype K] [Fintype Γ] [Fintype V] [Inhabited Λ] in
theorem advances_step (c c' : TM2.Cfg (fun _ : K=>Γ) Λ V) (h : c'∈TM2.step M c) :
    ∃t : ℕ,(advance M)^[t] (fromCfg M c)=fromCfg M c' := by
  rcases c with ⟨l,v,st⟩
  cases l with
  | none=>simp [TM2.step] at h
  | some l=>
    have he : c'=TM2.stepAux (M l) v st := by simpa [TM2.step,Option.mem_def] using (show TM2.stepAux (M l) v st = c' from by simpa [TM2.step,Option.mem_def] using h).symm
    subst c'
    exact advances_aux M (M l) v st

omit [Fintype K] [Fintype Γ] [Fintype V] [Inhabited Λ] in
theorem advances_reaches (c c' : TM2.Cfg (fun _ : K=>Γ) Λ V) (h : TM2.Reaches M c c') :
    ∃t : ℕ,(advance M)^[t] (fromCfg M c)=fromCfg M c' := by
  induction h with
  | refl=>exact ⟨0,rfl⟩
  | @tail b c' hab hbc ih=>
    obtain ⟨t,ht⟩:=ih
    obtain ⟨u,hu⟩:=advances_step M b c' hbc
    exact ⟨u+t,by rw [Function.iterate_add_apply,ht,hu]⟩

include hs in
omit [Fintype K] [Fintype Γ] [Fintype V] in
theorem iterate_supported (x : Runtime (K:=K) (Γ:=Γ) (Λ:=Λ) (V:=V))
    (hx : x.pc∈TM2.stmts M S) (t : ℕ) : ((advance M)^[t] x).pc∈TM2.stmts M S := by
  induction t generalizing x with
  | zero=>exact hx
  | succ t ih=>
    rw [Function.iterate_succ_apply]
    exact ih _ (advance_supported M S hs x hx)

theorem encode_run (v₀ : V) (x : Runtime (K:=K) (Γ:=Γ) (Λ:=Λ) (V:=V))
    (hx : x.pc∈TM2.stmts M S) (t : ℕ) :
    run (processor M S hs v₀) (encode M S x hx) (List.replicate t false)=
      encode M S ((advance M)^[t] x) (iterate_supported M S hs x hx t) := by
  induction t generalizing x with
  | zero=>rfl
  | succ t ih=>
    rw [List.replicate_succ,run_cons,encode_step]
    exact ih _ (advance_supported M S hs x hx)

omit [Fintype K] [Fintype Γ] [Fintype V] [DecidableEq K] [Inhabited Λ] in
theorem fromCfg_supported (c : TM2.Cfg (fun _ : K=>Γ) Λ V)
    (hc : c.l∈Finset.insertNone S) : (fromCfg M c).pc∈TM2.stmts M S := by
  rcases c with ⟨l,v,st⟩
  cases l with
  | none=>exact (done M S).property
  | some l=>exact (root M S l (Finset.some_mem_insertNone.mp hc)).property

/-- Halting is inherited by the actual finite-control stack processor. -/
theorem processor_halts (v₀ : V) (c c' : TM2.Cfg (fun _ : K=>Γ) Λ V)
    (hc : c.l∈Finset.insertNone S) (h : TM2.Reaches M c c') (hhalt : c'.l=none) :
    ∃t : ℕ, (run (processor M S hs v₀)
      (encode M S (fromCfg M c) (fromCfg_supported M S c hc)) (List.replicate t false)).yielded=true ∧
      ∀i, (run (processor M S hs v₀)
      (encode M S (fromCfg M c) (fromCfg_supported M S c hc)) (List.replicate t false)).store i=
        (c'.stk (keys.symm i)).map letters := by
  obtain ⟨t,ht⟩:=advances_reaches M c c' h
  refine ⟨t,?_,?_⟩
  · rw [encode_run]
    change ((advance M)^[t] (fromCfg M c)).pc.isNone=true
    rw [ht]
    simp [fromCfg,hhalt]
  · intro i
    rw [encode_run]
    change (((advance M)^[t] (fromCfg M c)).store (keys.symm i)).map letters=_
    rw [ht]
    rfl

end UniformKServer.FlatTM2

end

end OAI
