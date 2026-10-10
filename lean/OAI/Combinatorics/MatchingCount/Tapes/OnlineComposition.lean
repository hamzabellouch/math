import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeFrame
import OAI.Combinatorics.MatchingCount.Tapes.Online

namespace OAI

namespace MatchingFPRAS.OnlineStack
open Turing MachineCost PhysicalStream StackComposition

variable {K Λ Λ' σ α : Type} {Γ : K → Type} [DecidableEq K]
namespace Executes
lemma relabel {M : Λ → TM2.Stmt Γ Λ σ} {coin : CoinTM1.Coins Λ}
    {out : α → TM2.Cfg Γ Λ σ} {c : TM2.Cfg Γ Λ σ} {p : Experiment α}
    (h : Executes M coin out c p) (N : Λ' → TM2.Stmt Γ Λ' σ)
    (co : CoinTM1.Coins Λ') (f : Λ → Λ') (halt : Option Λ')
    (hN : ∀ l,N (f l)=StackComposition.relabel f halt (M l))
    (hco : ∀ l,co (f l)=(coin l).map (fun g=>f ∘ g)) :
    Executes N co (fun a=>mapCfg f halt (out a)) (mapCfg f halt c) p := by
  induction h with
  | done a => exact .done a
  | read l v S g p hg rest ih =>
    apply Executes.read (f l) v S (f ∘ g) p
    · rw [hco,hg]; rfl
    · exact ih
  | step l v S p hs rest ih =>
    apply Executes.step (f l) v S p
    · rw [hco,hs]; rfl
    · rw [hN,StackComposition.relabel_eval]
      exact ih

lemma of_run (M : Λ → TM2.Stmt Γ Λ σ) (n : ℕ) (c : TM2.Cfg Γ Λ σ)
    (v : σ) (S : ∀ k,List (Γ k)) (he : MachineCost.run (TM2.step M) n c=⟨none,v,S⟩) :
    ∃ p : Experiment Unit,Executes M (fun _=>none) (fun _ : Unit=>⟨none,v,S⟩) c p ∧
      (∀ f : Unit → ℚ,p.mean f=f ()) ∧ p.cost≤n := by
  induction n generalizing c with
  | zero => cases he; exact ⟨.done (),.done (),fun _=>rfl,le_rfl⟩
  | succ n ih =>
    rcases c with ⟨l,v',S'⟩
    cases l with
    | none =>
      rw [StackComposition.run_halted] at he
      cases he
      exact ⟨.done (),.done (),fun _=>rfl,Nat.zero_le _⟩
    | some l =>
      obtain ⟨p,hp,hm,hc⟩:=ih (TM2.stepAux (M l) v' S') he
      exact ⟨.delay 1 p,.step l v' S' p rfl hp,hm,by simpa [Experiment.cost,Nat.add_comm] using Nat.succ_le_succ hc⟩
end Executes
end MatchingFPRAS.OnlineStack

namespace MatchingFPRAS.OnlineProc
open Turing MachineCost PhysicalStream OnlineStack RegisterProc

variable {K : Type} [DecidableEq K]

structure Proc (K : Type) extends RegisterProc.Proc K where
  coin : CoinTM1.Coins Label

def deterministic (P : RegisterProc.Proc K) : Proc K := ⟨P,fun _=>none⟩
def seq (P Q : Proc K) : Proc K where
  toProc := RegisterProc.seq P.toProc Q.toProc
  coin := fun l=>match l with
    | .inl l => (P.coin l).map (fun f b=>Sum.inl (f b))
    | .inr l => (Q.coin l).map (fun f b=>Sum.inr (f b))

def Exec (P : Proc K) (S : Stack K) (p : Experiment (Stack K)) (bound : ℕ) : Prop :=
  ∃ q : Experiment (Stack K),
    Executes P.code P.coin (fun T=>⟨none,none,T⟩) ⟨some default,none,S⟩ q ∧
    (∀ f : Stack K → ℚ,q.mean f=p.mean f) ∧ q.cost≤bound

lemma exec_deterministic {P : RegisterProc.Proc K} {S T : Stack K} {n : ℕ}
    (h : RegisterProc.Exec P S T n) : Exec (deterministic P) S (.done T) n := by
  obtain ⟨k,hk,he⟩:=h
  obtain ⟨p,hp,hm,hc⟩:=Executes.of_run P.code k ⟨some default,none,S⟩ none T he
  refine ⟨p.map (fun _=>T),?_,?_,?_⟩
  · apply hp.bind (fun _=>.done T) (fun T=>⟨none,none,T⟩)
    intro _
    exact .done T
  · intro f
    rw [Experiment.mean_map,hm]; rfl
  · rw [Experiment.cost_map]
    exact hc.trans hk

lemma Exec.mono {P : Proc K} {S : Stack K} {p : Experiment (Stack K)} {n m : ℕ}
    (h : Exec P S p n) (hn : n ≤ m) : Exec P S p m := by
  obtain ⟨q,hq,hm,hc⟩:=h
  exact ⟨q,hq,hm,hc.trans hn⟩

lemma Exec.seq {P Q : Proc K} {S : Stack K} {p : Experiment (Stack K)}
    {q : Stack K → Experiment (Stack K)} {n m : ℕ}
    (hP : Exec P S p n) (hQ : ∀ T,Exec Q T (q T) m) :
    Exec (OnlineProc.seq P Q) S (p.bind q) (n+m) := by
  obtain ⟨p',hp',hpm,hpc⟩:=hP
  choose q' hq' hqm hqc using hQ
  have hp:=hp'.relabel (OnlineProc.seq P Q).code (OnlineProc.seq P Q).coin Sum.inl (some (Sum.inr default))
    (fun _=>rfl) (fun _=>rfl)
  have hq T := (hq' T).relabel (OnlineProc.seq P Q).code (OnlineProc.seq P Q).coin Sum.inr none
    (fun _=>rfl) (fun _=>rfl)
  refine ⟨p'.bind q',hp.bind q' _ hq,?_,?_⟩
  · intro f
    rw [Experiment.mean_bind,Experiment.mean_bind]
    simp_rw [hqm]
    exact hpm _
  · exact (Experiment.cost_bind_le p' q' m hqc).trans (Nat.add_le_add_right hpc m)
end MatchingFPRAS.OnlineProc

end OAI
