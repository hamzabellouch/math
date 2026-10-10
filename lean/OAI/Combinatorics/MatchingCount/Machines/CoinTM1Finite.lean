import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.CoinTM1
import OAI.Combinatorics.MatchingCount.Machines.PhysicalRestriction

namespace OAI

namespace MatchingFPRAS.CoinTM1
open Turing
open scoped Classical

variable {Γ Λ σ : Type} [Inhabited Λ] [Fintype σ]

noncomputable def nodes (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) : Finset (Node Γ Λ σ) :=
  S.disjSum (S.biUnion (fun l=>TM1.stmts₁ (M l)))
noncomputable def states (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) : Finset (State Γ Λ σ) :=
  (nodes M S) ×ˢ Finset.univ

omit [Inhabited Λ] [Fintype σ] in
lemma node_entry {M : Λ → TM1.Stmt Γ Λ σ} {S : Finset Λ} {l : Λ} (h : l∈S) :
    Sum.inl l∈nodes M S := by simp only [nodes,Finset.inl_mem_disjSum]; exact h
omit [Inhabited Λ] [Fintype σ] in
lemma node_pending {M : Λ → TM1.Stmt Γ Λ σ} {S : Finset Λ} {q : TM1.Stmt Γ Λ σ}
    (h : some q∈TM1.stmts M S) : Sum.inr q∈nodes M S := by
  simpa only [nodes,Finset.inr_mem_disjSum,TM1.stmts,Finset.some_mem_insertNone] using h
omit [Inhabited Λ] in
lemma state_mem {M : Λ → TM1.Stmt Γ Λ σ} {S : Finset Λ} {q : Node Γ Λ σ} {v : σ}
    (h : q∈nodes M S) : (q,v)∈states M S := by
  simp only [states,Finset.mem_product,Finset.mem_univ,and_true]; exact h

lemma aux_supported {M : Λ → TM1.Stmt Γ Λ σ} {S : Finset Λ}
    (hs : TM1.Supports M S) (a : Γ) (q : TM1.Stmt Γ Λ σ)
    (hq : some q∈TM1.stmts M S) (v : σ) (q' : State Γ Λ σ) (act : TM0.Stmt Γ)
    (he : aux a q v=some (q',act)) : q'∈states M S := by
  classical
  induction q generalizing v q' act with
  | move d q ih =>
    simp only [aux,Option.some.injEq,Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    apply state_mem
    apply node_pending
    exact TM1.stmts_trans (by simp only [TM1.stmts₁,Finset.mem_insert]; exact Or.inr TM1.stmts₁_self) hq
  | write f q ih =>
    simp only [aux,Option.some.injEq,Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    apply state_mem
    apply node_pending
    exact TM1.stmts_trans (by simp only [TM1.stmts₁,Finset.mem_insert]; exact Or.inr TM1.stmts₁_self) hq
  | load f q ih =>
    exact ih (TM1.stmts_trans (by simp only [TM1.stmts₁,Finset.mem_insert]; exact Or.inr TM1.stmts₁_self) hq) _ _ _ he
  | branch f q r ihq ihr =>
    simp only [aux] at he
    split_ifs at he with hf
    · exact ihq (TM1.stmts_trans (by simp only [TM1.stmts₁,Finset.mem_insert,Finset.mem_union]; exact Or.inr (Or.inl TM1.stmts₁_self)) hq) _ _ _ he
    · exact ihr (TM1.stmts_trans (by simp only [TM1.stmts₁,Finset.mem_insert,Finset.mem_union]; exact Or.inr (Or.inr TM1.stmts₁_self)) hq) _ _ _ he
  | goto f =>
    simp only [aux,Option.some.injEq,Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    exact state_mem (node_entry (TM1.stmts_supportsStmt hs hq a v))
  | halt => simp [aux] at he

theorem table_supported (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hs : TM1.Supports M S)
    (coin : Coins Λ) (hc : ∀ l∈S,∀ f,coin l=some f→∀ b,f b∈S) :
    PhysicalPost.Supported (table M coin) (states M S) := by
  intro q hq a b q' act he
  have hn : q.1∈nodes M S := (Finset.mem_product.mp hq).1
  rcases q with ⟨l,v⟩
  cases l with
  | inl l =>
    have hl : l∈S := by simpa only [nodes,Finset.inl_mem_disjSum] using hn
    simp only [table] at he
    split at he
    · apply aux_supported hs a (M l) _ v q' act he
      simp only [TM1.stmts,Finset.some_mem_insertNone,Finset.mem_biUnion]
      exact ⟨l,hl,TM1.stmts₁_self⟩
    · rename_i f hf
      simp only [Option.some.injEq,Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl⟩
      exact state_mem (node_entry (hc l hl f hf b))
  | inr q =>
    apply aux_supported hs a q _ v q' act he
    simpa only [nodes,Finset.inr_mem_disjSum,TM1.stmts,Finset.some_mem_insertNone] using hn

end MatchingFPRAS.CoinTM1

end OAI
