import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.CoinTM1Finite
import OAI.Combinatorics.MatchingCount.Tapes.TapeTools
import OAI.Combinatorics.MatchingCount.Machines.PhysicalProcess
import OAI.Combinatorics.MatchingCount.Graphs.SafeTrace

namespace OAI

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost PhysicalStream

variable {Γ Λ σ : Type} [Inhabited Γ] [Inhabited Λ] [Fintype Λ] [Fintype σ] [Inhabited σ]
omit [Inhabited Γ] [Fintype σ] [Inhabited σ] in
lemma supports_univ (M : Λ→TM1.Stmt Γ Λ σ) : TM1.Supports M Finset.univ := by
  classical
  refine ⟨Finset.mem_univ _,fun l _=>?_⟩
  induction M l with
  | move d q ih => exact ih
  | write f q ih => exact ih
  | load f q ih => exact ih
  | branch f q r ih jh => exact ⟨ih,jh⟩
  | goto f => exact fun a v=>Finset.mem_univ _
  | halt => trivial
noncomputable def table (M : Λ→TM1.Stmt Γ Λ σ) := CoinTM1.table M (fun _=>none)
noncomputable def states (M : Λ→TM1.Stmt Γ Λ σ) := CoinTM1.states M Finset.univ
omit [Inhabited Γ] [Inhabited σ] in
lemma supported (M : Λ→TM1.Stmt Γ Λ σ) : PhysicalPost.Supported (table M) (states M) :=
  CoinTM1.table_supported M Finset.univ (supports_univ M) (fun _=>none) (by simp)
omit [Inhabited Γ] [Inhabited Λ] [Inhabited σ] in
lemma entry_mem (M : Λ→TM1.Stmt Γ Λ σ) (l : Λ) (v : σ) : (Sum.inl l,v)∈states M :=
  CoinTM1.state_mem (CoinTM1.node_entry (Finset.mem_univ _))
omit [Inhabited Λ] [Fintype σ] [Inhabited σ] in
lemma Exec.physical {M : Λ→TM1.Stmt Γ Λ σ} {c d : TM1.Cfg Γ Λ σ} {t : ℕ}
    (h : Exec M c d t) : ∃ k,k≤t*programCost M ∧ ∀ b : Stream,
      PhysicalPost.execute (table M) k (CoinTM1.trCfg c) b=CoinTM1.trCfg d := by
  obtain ⟨n,hn,he⟩:=h
  have hp:=SafeTrace.Path.of_run (safe:=fun _=>True) (M:=M) n c (fun _ _ _ _=>trivial)
  rw [he] at hp
  obtain ⟨k,hk,hb⟩:=hp.physical (fun _=>none) (fun _ _=>rfl) (programCost M)
    (fun l _=>statementCost_le_programCost M l)
  exact ⟨k,hk.trans (Nat.mul_le_mul_right _ hn),hb⟩
omit [Inhabited Λ] [Fintype σ] [Inhabited σ] in
lemma Exec.implements {M : Λ→TM1.Stmt Γ Λ σ} {c d : TM1.Cfg Γ Λ σ} {t : ℕ}
    (h : Exec M c d t) : ∃ p : Experiment Unit,p.cost≤t*programCost M ∧
      PhysicalPost.Implements (table M) (fun _=>CoinTM1.trCfg d) (CoinTM1.trCfg c) p ∧
      ∀ f : Unit→ℚ,p.mean f=f () := by
  obtain ⟨k,hk,hb⟩:=h.physical
  exact ⟨.delay k (.done ()),by simpa only [Experiment.cost,Nat.add_zero] using hk,.delay _ _ k _ hb (.done ()),fun _=>rfl⟩
end MatchingFPRAS.LiteralTape

end OAI
