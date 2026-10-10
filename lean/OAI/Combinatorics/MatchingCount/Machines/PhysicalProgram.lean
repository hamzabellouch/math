import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.ExperimentSupport
import OAI.Combinatorics.MatchingCount.Machines.PhysicalSequential
import OAI.Combinatorics.MatchingCount.Tapes.Physical

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {A : Type}
lemma mean_congr_all (p : Experiment A) (f g : A→ℚ) (h : p.All (fun a=>f a=g a)) : p.mean f=p.mean g := by
  induction p with
  | done a => exact h
  | delay n p ih => exact ih h
  | read p ih => simp only [mean,ih false h.1,ih true h.2]
end MatchingFPRAS.PhysicalStream.Experiment

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q A B : Type} [Inhabited Γ]
lemma Implements.map_all {M : Table Γ Q} {out : A→Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment A} (h : Implements M out c p) (f : A→B) (out' : B→Cfg Γ Q)
    (he : p.All (fun a=>out a=out' (f a))) : Implements M out' c (p.map f) := by
  induction h with
  | done a => rw [he];exact .done (f a)
  | read c p h ih => exact .read _ _ (fun b=>by cases b;exact ih false he.1;exact ih true he.2)
  | delay c d n p hs hr ih => exact .delay _ _ n _ hs (ih he)
lemma early_implements (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) : Implements M id c (early M n c) := by
  induction n generalizing c with
  | zero => exact .done c
  | succ n ih =>
    rcases c with ⟨s,T⟩
    cases s with
    | none => exact .done _
    | some q => exact .read _ _ (fun b=>ih _)
lemma Implements.early_all {M : Table Γ Q} {out : A→Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment A} (h : Implements M out c p) (halt : ∀ a,(out a).state=none)
    (n : ℕ) (hn : p.cost≤n) : (early M n c).All (fun d=>d.state=none) := by
  apply Experiment.all_of_mean_eq (p:=(p.map out)) (fun f=>by rw [Experiment.mean_map];exact h.early_mean halt n hn f)
  rw [Experiment.all_map]
  exact (Experiment.all_true _).mono (fun a _=>halt a)

structure Program where
  State : Type
  table : Table Symbol State
  states : Finset State
  supported : Supported table states
  entry : State
  entry_mem : entry∈states
namespace Program
noncomputable def seq (P R : Program) : Program where
  State := P.State⊕R.State
  table := PhysicalPost.seq P.table R.table R.entry
  states := P.states.disjSum R.states
  supported := seq_supported _ _ _ _ _ P.supported R.supported R.entry_mem
  entry := .inl P.entry
  entry_mem := Finset.inl_mem_disjSum.mpr P.entry_mem
noncomputable def machine (P : Program) : RandomMachine :=
  restrictedMachine P.table P.states P.supported P.entry P.entry_mem

def initial (P : Program) (T : Tape Symbol) : Cfg Symbol P.State := ⟨some P.entry,T⟩
def final (P : Program) (T : Tape Symbol) : Cfg Symbol P.State := ⟨none,T⟩
def Realizes (P : Program) (input : Tape Symbol) (f : Experiment (Tape Symbol)) (N : ℕ) : Prop :=
  ∃ p : Experiment (Tape Symbol),Implements P.table P.final (P.initial input) p ∧
    (∀ h,p.mean h=f.mean h) ∧ p.cost≤N

def earlyTapes (P : Program) (n : ℕ) (T : Tape Symbol) : Experiment (Tape Symbol) :=
  (early P.table n (P.initial T)).map Cfg.tape
lemma earlyTapes_cost (P : Program) (n : ℕ) (T : Tape Symbol) : (P.earlyTapes n T).cost≤n := by
  rw [earlyTapes,Experiment.cost_map];exact early_cost _ _ _
lemma Realizes.early {P : Program} {input : Tape Symbol} {f : Experiment (Tape Symbol)} {N : ℕ}
    (h : P.Realizes input f N) :
    Implements P.table P.final (P.initial input) (P.earlyTapes N input) ∧
      (∀ w,(P.earlyTapes N input).mean w=f.mean w) := by
  obtain ⟨p,hp,hm,hc⟩:=h
  refine ⟨?_,fun w=>?_⟩
  · apply (early_implements P.table N (P.initial input)).map_all Cfg.tape P.final
    exact (hp.early_all (fun _=>rfl) N hc).mono (by intro d hd;cases d; simp only [id_eq,final] at *;cases hd;rfl)
  · rw [earlyTapes,Experiment.mean_map,hp.early_mean (fun _=>rfl) N hc]
    exact hm w
lemma seq_realizes (P R : Program) (input : Tape Symbol) (f : Experiment (Tape Symbol))
    (g : Tape Symbol→Experiment (Tape Symbol)) (N S : ℕ)
    (hP : P.Realizes input f N) (hR : f.All (fun T=>R.Realizes T (g T) S)) :
    (P.seq R).Realizes input (f.bind g) (N+S) := by
  let p:=early P.table N (P.initial input)
  let q:=fun c : Cfg Symbol P.State=>R.earlyTapes S c.tape
  have hmean (h : Cfg Symbol P.State→ℚ) : p.mean h=f.mean (fun T=>h (P.final T)) := by
    obtain ⟨v,hv,hm,hc⟩:=hP
    rw [hv.early_mean (fun _=>rfl) N hc]
    exact hm _
  have hall : p.All (fun c=>c.state=none ∧ R.Realizes c.tape (g c.tape) S) := by
    apply Experiment.all_of_mean_eq (p:=f.map P.final) (fun h=>by rw [Experiment.mean_map];exact hmean h)
    rw [Experiment.all_map]
    exact hR.mono (fun T hT=>⟨rfl,hT⟩)
  have himpl : Implements (P.seq R).table (fun T=>rightCfg (R.final T))
      ((P.seq R).initial input) (p.bind q) := by
    apply (early_left P.table R.table R.entry N (P.initial input)).bind_all q _
    exact hall.mono (by
      intro c hc
      have hq:=(hc.2.early).1.right (M:=P.table) R.entry
      have he:leftCfg R.entry c=rightCfg (R.initial c.tape) := by
        rcases c with ⟨s,T⟩;simp only at hc;cases hc.1;rfl
      rw [he]
      exact hq)
  refine ⟨p.bind q,himpl,?_,?_⟩
  · intro w
    rw [Experiment.mean_bind,hmean,Experiment.mean_bind]
    apply Experiment.mean_congr_all
    exact hR.mono (fun T hT=>hT.early.2 w)
  · exact (Experiment.cost_bind_le p q S (fun c=>earlyTapes_cost R S c.tape)).trans
      (Nat.add_le_add_right (early_cost _ N _) S)

noncomputable def ofTM1 {Λ σ : Type} [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ]
    (M : Λ→TM1.Stmt Symbol Λ σ) (l : Λ) (v : σ) : Program where
  State := CoinTM1.State Symbol Λ σ
  table := LiteralTape.table M
  states := LiteralTape.states M
  supported := LiteralTape.supported M
  entry := (.inl l,v)
  entry_mem := LiteralTape.entry_mem M l v
lemma realizes_TM1 {Λ σ : Type} [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ]
    (M : Λ→TM1.Stmt Symbol Λ σ) (l : Λ) (v v' : σ) (input output : Tape Symbol) (n : ℕ)
    (he : LiteralTape.Exec M ⟨some l,v,input⟩ ⟨none,v',output⟩ n) :
    (ofTM1 M l v).Realizes input (.done output) (n*MachineCost.programCost M) := by
  obtain ⟨k,hk,hb⟩:=he.physical
  refine ⟨.delay k (.done output),?_,fun _=>rfl,by simpa only [Experiment.cost,Nat.add_zero] using hk⟩
  exact .delay _ _ k _ hb (.done output)
end Program
end MatchingFPRAS.PhysicalPost

end OAI
