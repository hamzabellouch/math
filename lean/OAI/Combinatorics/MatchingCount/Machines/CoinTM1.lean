import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.GuardMachineBase
import OAI.Combinatorics.MatchingCount.Machines.PhysicalPost

namespace OAI

namespace MatchingFPRAS.CoinTM1
open Turing MachineCost PhysicalStream

variable {Γ Λ σ : Type} [Inhabited Γ]

abbrev Node (Γ Λ σ : Type) := Λ ⊕ TM1.Stmt Γ Λ σ
abbrev State (Γ Λ σ : Type) := Node Γ Λ σ × σ
abbrev Coins (Λ : Type) := Λ → Option (Bool → Λ)

def aux (a : Γ) : TM1.Stmt Γ Λ σ → σ → Option (State Γ Λ σ × TM0.Stmt Γ)
  | .move d q,v => some ((.inr q,v),.move d)
  | .write f q,v => some ((.inr q,v),.write (f a v))
  | .load f q,v => aux a q (f a v)
  | .branch f q r,v => if f a v then aux a q v else aux a r v
  | .goto f,v => some ((.inl (f a v),v),.write a)
  | .halt,_ => none

def table (M : Λ → TM1.Stmt Γ Λ σ) (coin : Coins Λ) : PhysicalPost.Table Γ (State Γ Λ σ)
  | (.inl l,v),a,b => match coin l with
    | none => aux a (M l) v
    | some f => some ((.inl (f b),v),.write a)
  | (.inr q,v),a,_ => aux a q v

def pending (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) : PhysicalPost.Cfg Γ (State Γ Λ σ) :=
  ⟨some (.inr q,v),T⟩

def trCfg (c : TM1.Cfg Γ Λ σ) : PhysicalPost.Cfg Γ (State Γ Λ σ) :=
  ⟨c.l.map (fun l=>(Sum.inl l,c.var)),c.Tape⟩

lemma execute_first_eq (M : PhysicalPost.Table Γ (State Γ Λ σ))
    (x y : PhysicalPost.Cfg Γ (State Γ Λ σ)) (h : ∀ b,PhysicalPost.tick M x b=PhysicalPost.tick M y b)
    {n : ℕ} (hn : 0 < n) (b : Stream) : PhysicalPost.execute M n x b=PhysicalPost.execute M n y b := by
  cases n with
  | zero => omega
  | succ n => simp only [PhysicalPost.execute,h]

theorem statement_ticks (M : Λ → TM1.Stmt Γ Λ σ) (coin : Coins Λ)
    (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    ∃ k,0 < k ∧ k ≤ statementCost q ∧ ∀ b : Stream,
      PhysicalPost.execute (table M coin) k (pending q v T) b=trCfg (TM1.stepAux q v T) := by
  induction q generalizing v T with
  | move d q ih =>
    obtain ⟨k,hk,hc,he⟩:=ih v (T.move d)
    refine ⟨k+1,by omega,by simp only [statementCost]; omega,fun b=>?_⟩
    simpa only [PhysicalPost.execute,PhysicalPost.tick,pending,table,aux,TM1.stepAux] using he (shift 1 b)
  | write f q ih =>
    obtain ⟨k,hk,hc,he⟩:=ih v (T.write (f T.head v))
    refine ⟨k+1,by omega,by simp only [statementCost]; omega,fun b=>?_⟩
    simpa only [PhysicalPost.execute,PhysicalPost.tick,pending,table,aux,TM1.stepAux] using he (shift 1 b)
  | load f q ih =>
    obtain ⟨k,hk,hc,he⟩:=ih (f T.head v) T
    refine ⟨k,hk,hc,fun b=>?_⟩
    rw [execute_first_eq (table M coin) (pending (.load f q) v T) (pending q (f T.head v) T) (fun _=>rfl) hk]
    exact he b
  | branch f q r ihq ihr =>
    cases h:f T.head v with
    | false =>
      obtain ⟨k,hk,hc,he⟩:=ihr v T
      refine ⟨k,hk,hc.trans (le_max_right _ _),fun b=>?_⟩
      rw [execute_first_eq (table M coin) (pending (.branch f q r) v T) (pending r v T) (fun _=>by
        simp only [PhysicalPost.tick,pending,table,aux,h,Bool.false_eq_true,ite_false]) hk]
      simpa only [TM1.stepAux,h,Bool.cond_false] using he b
    | true =>
      obtain ⟨k,hk,hc,he⟩:=ihq v T
      refine ⟨k,hk,hc.trans (le_max_left _ _),fun b=>?_⟩
      rw [execute_first_eq (table M coin) (pending (.branch f q r) v T) (pending q v T) (fun _=>by
        simp only [PhysicalPost.tick,pending,table,aux,h,ite_true]) hk]
      simpa only [TM1.stepAux,h,Bool.cond_true] using he b
  | goto f =>
    refine ⟨1,by omega,le_rfl,fun b=>?_⟩
    simp only [PhysicalPost.execute,PhysicalPost.tick,pending,table,aux,TM1.stepAux,trCfg,Option.map_some,Tape.write_self]
  | halt =>
    refine ⟨1,by omega,le_rfl,fun b=>?_⟩
    rfl

lemma entry_ticks (M : Λ → TM1.Stmt Γ Λ σ) (coin : Coins Λ)
    (l : Λ) (v : σ) (T : Tape Γ) (hl : coin l=none) :
    ∃ k,0 < k ∧ k ≤ statementCost (M l) ∧ ∀ b : Stream,
      PhysicalPost.execute (table M coin) k (trCfg ⟨some l,v,T⟩) b=
        trCfg (TM1.stepAux (M l) v T) := by
  obtain ⟨k,hk,hc,he⟩:=statement_ticks M coin (M l) v T
  refine ⟨k,hk,hc,fun b=>?_⟩
  rw [execute_first_eq (table M coin) (trCfg ⟨some l,v,T⟩) (pending (M l) v T) (fun _=>by
    simp only [PhysicalPost.tick,trCfg,Option.map_some,table,hl,pending]) hk]
  exact he b

lemma coin_tick (M : Λ → TM1.Stmt Γ Λ σ) (coin : Coins Λ)
    (l : Λ) (v : σ) (T : Tape Γ) (f : Bool → Λ) (hl : coin l=some f) (b : Bool) :
    PhysicalPost.tick (table M coin) (trCfg ⟨some l,v,T⟩) b=trCfg ⟨some (f b),v,T⟩ := by
  simp only [PhysicalPost.tick,trCfg,Option.map_some,table,hl,Tape.write_self]

end MatchingFPRAS.CoinTM1

end OAI
