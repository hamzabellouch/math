import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.GuardMachineBase

namespace OAI

namespace MatchingFPRAS.ProgramComposition
open Turing MachineCost

variable {Γ Λ Κ σ : Type*} [Inhabited Γ]

def relabel (f : Λ → Κ) (h : Option Κ) : TM1.Stmt Γ Λ σ → TM1.Stmt Γ Κ σ
  | .move d q => .move d (relabel f h q)
  | .write a q => .write a (relabel f h q)
  | .load a q => .load a (relabel f h q)
  | .branch p q r => .branch p (relabel f h q) (relabel f h r)
  | .goto l => .goto (fun a v=>f (l a v))
  | .halt => match h with | none=>.halt | some k=>.goto (fun _ _=>k)
def mapCfg (f : Λ → Κ) (h : Option Κ) (c : TM1.Cfg Γ Λ σ) : TM1.Cfg Γ Κ σ :=
  ⟨c.l.bind (fun l=>some (f l)) |>.or h,c.var,c.Tape⟩
lemma mapCfg_some (f : Λ → Κ) (h : Option Κ) (l : Λ) (v : σ) (T : Tape Γ) :
    mapCfg f h ⟨some l,v,T⟩=⟨some (f l),v,T⟩ := rfl
lemma mapCfg_none (f : Λ → Κ) (h : Option Κ) (v : σ) (T : Tape Γ) :
    mapCfg f h ⟨none,v,T⟩=⟨h,v,T⟩ := rfl
lemma relabel_eval (f : Λ → Κ) (h : Option Κ) (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    TM1.stepAux (relabel f h q) v T=mapCfg f h (TM1.stepAux q v T) := by
  induction q generalizing v T with
  | move d q ih => exact ih v (T.move d)
  | write a q ih => exact ih v (T.write (a T.head v))
  | load a q ih => exact ih (a T.head v) T
  | branch p q r ihq ihr => cases hp:p T.head v <;> simp only [relabel,TM1.stepAux,hp,Bool.cond_false,Bool.cond_true] <;> first | apply ihr | apply ihq
  | goto l => rfl
  | halt => cases h <;> rfl
omit [Inhabited Γ] in
lemma relabel_cost (f : Λ → Κ) (h : Option Κ) (q : TM1.Stmt Γ Λ σ) :
    statementCost (relabel f h q)=statementCost q := by
  induction q with
  | move d q ih | write d q ih | load d q ih => simp only [relabel,statementCost,ih]
  | branch p q r ihq ihr => simp only [relabel,statementCost,ihq,ihr]
  | goto l => rfl
  | halt => cases h <;> rfl
lemma run_halted (M : Λ → TM1.Stmt Γ Λ σ) (n : ℕ) (v : σ) (T : Tape Γ) :
    MachineCost.run (TM1.step M) n ⟨none,v,T⟩=⟨none,v,T⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [MachineCost.run,advance,TM1.step,Option.getD_none] using ih

lemma run_relabel_to_halt (M : Λ → TM1.Stmt Γ Λ σ) (N : Κ → TM1.Stmt Γ Κ σ)
    (f : Λ → Κ) (h : Option Κ) (hN : ∀ l,N (f l)=relabel f h (M l))
    (n : ℕ) (c : TM1.Cfg Γ Λ σ) (v : σ) (T : Tape Γ)
    (he : MachineCost.run (TM1.step M) n c=⟨none,v,T⟩) :
    ∃ k≤n,MachineCost.run (TM1.step N) k (mapCfg f h c)=⟨h,v,T⟩ := by
  induction n generalizing c with
  | zero =>
    have hc : c=⟨none,v,T⟩:=he
    subst c
    exact ⟨0,le_rfl,rfl⟩
  | succ n ih =>
    rcases c with ⟨l,v',T'⟩
    cases l with
    | none =>
      rw [run_halted] at he
      cases he
      exact ⟨0,Nat.zero_le _,rfl⟩
    | some l =>
      have he' : MachineCost.run (TM1.step M) n (TM1.stepAux (M l) v' T')=⟨none,v,T⟩ := he
      obtain ⟨k,hk,hh⟩:=ih _ he'
      refine ⟨k+1,by omega,?_⟩
      rw [MachineCost.run,mapCfg_some]
      have hs : advance (TM1.step N) ⟨some (f l),v',T'⟩=
          mapCfg f h (TM1.stepAux (M l) v' T') := by
        simp only [advance,TM1.step,Option.getD_some,hN,relabel_eval]
      rw [hs,hh]
variable [Inhabited Λ] [Inhabited Κ]

def sequence (M : Λ → TM1.Stmt Γ Λ σ) (N : Κ → TM1.Stmt Γ Κ σ) :
    Λ⊕Κ → TM1.Stmt Γ (Λ⊕Κ) σ
  | .inl l => relabel Sum.inl (some (Sum.inr default)) (M l)
  | .inr k => relabel Sum.inr none (N k)
omit [Inhabited Λ] in
lemma sequence_run (M : Λ → TM1.Stmt Γ Λ σ) (N : Κ → TM1.Stmt Γ Κ σ)
    (c : TM1.Cfg Γ Λ σ) (m n : ℕ) (v v' : σ) (T T' : Tape Γ)
    (hM : MachineCost.run (TM1.step M) m c=⟨none,v,T⟩)
    (hN : MachineCost.run (TM1.step N) n ⟨some default,v,T⟩=⟨none,v',T'⟩) :
    ∃ k ≤ m+n,MachineCost.run (TM1.step (sequence M N)) k
      (mapCfg Sum.inl (some (Sum.inr default)) c)=⟨none,v',T'⟩ := by
  obtain ⟨i,hi,hei⟩:=run_relabel_to_halt M (sequence M N) Sum.inl
    (some (Sum.inr default)) (fun _=>rfl) m c v T hM
  obtain ⟨j,hj,hej⟩:=run_relabel_to_halt N (sequence M N) Sum.inr
    none (fun _=>rfl) n ⟨some default,v,T⟩ v' T' hN
  refine ⟨i+j,by omega,?_⟩
  rw [run_add,hei]
  exact hej
omit [Inhabited Γ] [Inhabited Λ] in
lemma sequence_cost [Inhabited σ] [Fintype Λ] [Fintype Κ]
    (M : Λ → TM1.Stmt Γ Λ σ) (N : Κ → TM1.Stmt Γ Κ σ) :
    programCost (sequence M N) ≤ max (programCost M) (programCost N) := by
  apply Finset.sup_le
  intro l _
  cases l with
  | inl l => exact (by rw [sequence,relabel_cost]; exact (statementCost_le_programCost M l).trans (le_max_left _ _))
  | inr k => exact (by rw [sequence,relabel_cost]; exact (statementCost_le_programCost N k).trans (le_max_right _ _))
end MatchingFPRAS.ProgramComposition

end OAI
