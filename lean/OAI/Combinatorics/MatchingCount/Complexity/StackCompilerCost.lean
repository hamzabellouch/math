import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.GuardMachineBase

namespace OAI

namespace MatchingFPRAS.StackCost
open Turing Turing.TM2to1 Turing.TM2to1.Λ' MachineCost

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

def accesses : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => accesses q+1
  | .peek _ _ q => accesses q+1
  | .pop _ _ q => accesses q+1
  | .load _ q => accesses q
  | .branch _ q r => max (accesses q) (accesses r)
  | .goto _ => 0
  | .halt => 0
def StackBound (S : ∀ k,List (Γ k)) (H : ℕ) : Prop := ∀ k,(S k).length≤H
omit [DecidableEq K] in
lemma accesses_run {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    accesses (stRun o q)=accesses q+1 := by cases o <;> rfl
variable (M : Λ → TM2.Stmt Γ Λ σ)
lemma go_time {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    {S : List (Γ k)} {L : ListBlank (∀ k,Option (Γ k))}
    (hL : L.map (proj k)=ListBlank.mk (S.map some).reverse)
    (n : ℕ) (hn : n≤S.length) :
    MachineCost.run (TM1.step (tr M)) n ⟨some (go k o q),v,Tape.mk' ∅ (addBottom L)⟩=
      ⟨some (go k o q),v,(Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show n+1=n+1 from rfl,run_add,ih (by omega)]
    simp only [MachineCost.run,advance,TM1.step]
    rw [tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,addBottom_nth_snd,
      stk_nth_val _ hL,List.getElem?_eq_getElem (by simpa using (show n<S.length by omega))]
    simp only [Option.isNone_some,Bool.cond_false,TM1.stepAux,Option.getD_some]
    rw [Function.iterate_succ_apply']
lemma return_time (q : TM2.Stmt Γ Λ σ) (v : σ) (L : ListBlank (∀ k,Option (Γ k))) (n : ℕ) :
    MachineCost.run (TM1.step (tr M)) n
      ⟨some (ret q),v,(Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))⟩=
      ⟨some (ret q),v,Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [MachineCost.run]
    have hs : advance (TM1.step (tr M))
        ⟨some (ret q),v,(Tape.move .right)^[n+1] (Tape.mk' ∅ (addBottom L))⟩=
        ⟨some (ret q),v,(Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
      simp only [advance,TM1.step,tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,
        addBottom_nth_succ_fst,Bool.cond_false]
      rw [Function.iterate_succ_apply',Tape.move_right_left]
      rfl
    rw [hs,ih]
lemma action_bound {S : ∀ k,List (Γ k)} {H : ℕ} (hS : StackBound S H)
    {k : K} (o : StAct K Γ σ k) (v : σ) :
    StackBound (Function.update S k (stWrite v (S k) o)) (H+1) := by
  intro j
  by_cases hj : j=k
  · subst j
    rw [Function.update_self]
    have hk:=hS k
    cases o <;> simp only [stWrite,List.length_cons,List.length_tail] <;> omega
  · rw [Function.update_of_ne hj]
    exact (hS j).trans (by omega)
lemma stepAux_bound (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k,List (Γ k))
    (H : ℕ) (hS : StackBound S H) : StackBound (TM2.stepAux q v S).stk (H+accesses q) := by
  induction q using stmtStRec generalizing v S H with
  | run k o q ih =>
    rw [step_run,accesses_run]
    have hh:=ih (stVar v (S k) o) _ (H+1) (action_bound hS o v)
    convert hh using 1; omega
  | load a q ih => exact ih (a v) S H hS
  | branch p q r ihq ihr =>
    cases hp:p v
    · simp only [TM2.stepAux,hp,Bool.cond_false,accesses]
      exact fun k=>(ihr v S H hS k).trans (Nat.add_le_add_left (le_max_right _ _) H)
    · simp only [TM2.stepAux,hp,Bool.cond_true,accesses]
      exact fun k=>(ihq v S H hS k).trans (Nat.add_le_add_left (le_max_left _ _) H)
  | goto f => simpa only [TM2.stepAux,accesses,Nat.add_zero] using hS
  | halt => simpa only [TM2.stepAux,accesses,Nat.add_zero] using hS

theorem statement_time (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k,List (Γ k))
    (L : ListBlank (∀ k,Option (Γ k))) (H : ℕ) (hS : StackBound S H)
    (hL : ∀ k,L.map (proj k)=ListBlank.mk ((S k).map some).reverse) :
    ∃ (t : ℕ) (b : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ),
      t≤2*accesses q*(H+accesses q+1) ∧ TrCfg (TM2.stepAux q v S) b ∧
      MachineCost.run (TM1.step (tr M)) t
        (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom L)))=b := by
  induction q using stmtStRec generalizing v S L H with
  | run k o q ih =>
    let v':=stVar v (S k) o
    let S':=Function.update S k (stWrite v (S k) o)
    have hS' : StackBound S' (H+1):=action_bound hS o v
    obtain ⟨L',hL',hact⟩:=tr_respects_aux₂
      (q:=TM1.Stmt.goto fun _ _=>ret q) hL o
    obtain ⟨t,b,ht,hb,he⟩:=ih v' S' L' (H+1) hS' hL'
    have hgo:=go_time M o q v (hL k) (S k).length le_rfl
    have hs : advance (TM1.step (tr M))
        ⟨some (go k o q),v,(Tape.move .right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩=
        ⟨some (ret q),v',(Tape.move .right)^[(S' k).length] (Tape.mk' ∅ (addBottom L'))⟩ := by
      simp only [advance,TM1.step]
      rw [tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,addBottom_nth_snd,
        stk_nth_val _ (hL k),List.getElem?_eq_none (le_of_eq List.length_reverse)]
      simp only [Option.isNone_none,Bool.cond_true]
      rw [hact]
      rfl
    have hr : MachineCost.run (TM1.step (tr M))
        ((S k).length+1+(S' k).length+1)
        ⟨some (go k o q),v,Tape.mk' ∅ (addBottom L)⟩=
        TM1.stepAux (trNormal q) v' (Tape.mk' ∅ (addBottom L')) := by
      rw [run_add _ ((S k).length+1+(S' k).length) 1,
        run_add _ ((S k).length+1) (S' k).length,
        run_add _ (S k).length 1,hgo]
      simp only [MachineCost.run]
      rw [hs,return_time]
      simp only [advance,TM1.step,tr,TM1.stepAux,Tape.mk'_head,addBottom_head_fst,
        Bool.cond_true,Option.getD_some]
    refine ⟨(S k).length+1+(S' k).length+1+t,b,?_,?_,?_⟩
    · rw [accesses_run]
      have h₁:=hS k
      have h₂:=hS' k
      nlinarith
    · simpa only [step_run] using hb
    · rw [trNormal_run,TM1.stepAux,run_add,hr,he]
  | load a q ih => exact ih (a v) S L H hS hL
  | branch p q r ihq ihr =>
    cases hp:p v
    · obtain ⟨t,b,ht,hb,he⟩:=ihr v S L H hS hL
      refine ⟨t,b,ht.trans ?_,?_,?_⟩
      · simp only [accesses]; gcongr <;> exact le_max_right _ _
      · simpa only [TM2.stepAux,hp,Bool.cond_false] using hb
      · simpa only [trNormal,TM1.stepAux,hp,Bool.cond_false] using he
    · obtain ⟨t,b,ht,hb,he⟩:=ihq v S L H hS hL
      refine ⟨t,b,ht.trans ?_,?_,?_⟩
      · simp only [accesses]; gcongr <;> exact le_max_left _ _
      · simpa only [TM2.stepAux,hp,Bool.cond_true] using hb
      · simpa only [trNormal,TM1.stepAux,hp,Bool.cond_true] using he
  | goto f => exact ⟨0,_,Nat.zero_le _,⟨L,hL⟩,rfl⟩
  | halt => exact ⟨0,_,Nat.zero_le _,⟨L,hL⟩,rfl⟩

lemma advance_bound (A : ℕ) (hA : ∀ l,accesses (M l)≤A)
    (c : TM2.Cfg Γ Λ σ) (H : ℕ) (hS : StackBound c.stk H) :
    StackBound (advance (TM2.step M) c).stk (H+A) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => exact fun k=>(hS k).trans (Nat.le_add_right H A)
  | some l =>
    have hh:=stepAux_bound (M l) v S H hS
    exact fun k=>(hh k).trans (Nat.add_le_add_left (hA l) H)
lemma one_step_time (A : ℕ) (hA : ∀ l,accesses (M l)≤A)
    {c : TM2.Cfg Γ Λ σ} {a : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ}
    (hca : TrCfg c a) (H : ℕ) (hS : StackBound c.stk H) :
    ∃ (t : ℕ) (b : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ),
      t≤1+2*A*(H+A+1) ∧ TrCfg (advance (TM2.step M) c) b ∧
      MachineCost.run (TM1.step (tr M)) t a=b := by
  rcases hca with ⟨L,hL⟩
  rename_i l v S
  cases l with
  | none => exact ⟨0,_,Nat.zero_le _,⟨L,hL⟩,rfl⟩
  | some l =>
    obtain ⟨t,b,ht,hb,he⟩:=statement_time M (M l) v S L H hS hL
    refine ⟨t+1,b,?_,hb,?_⟩
    · have hh : 2*accesses (M l)*(H+accesses (M l)+1)≤2*A*(H+A+1) := by
        gcongr <;> exact hA l
      omega
    · simpa only [MachineCost.run,advance,TM1.step,Option.map_some,tr,Option.getD_some] using he

theorem execution_time (A : ℕ) (hA : ∀ l,accesses (M l)≤A)
    {c : TM2.Cfg Γ Λ σ} {a : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ}
    (hca : TrCfg c a) (H : ℕ) (hS : StackBound c.stk H) (n : ℕ) :
    ∃ (t : ℕ) (b : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ),
      t≤n*(1+2*A*(H+n*A+1)) ∧ TrCfg (MachineCost.run (TM2.step M) n c) b ∧
      MachineCost.run (TM1.step (tr M)) t a=b := by
  induction n generalizing c a H with
  | zero => exact ⟨0,a,by simp,hca,rfl⟩
  | succ n ih =>
    obtain ⟨t₁,b₁,ht₁,hb₁,he₁⟩:=one_step_time M A hA hca H hS
    obtain ⟨t₂,b₂,ht₂,hb₂,he₂⟩:=ih hb₁ (H+A) (advance_bound M A hA c H hS)
    refine ⟨t₁+t₂,b₂,?_,hb₂,?_⟩
    · have hcommon : 1+2*A*(H+A+1)≤1+2*A*(H+(n+1)*A+1) := by
        gcongr
        simp only [Nat.add_mul,Nat.one_mul]
        omega
      have heq : H+A+n*A+1=H+(n+1)*A+1 := by ring
      rw [heq] at ht₂
      calc
        t₁+t₂≤(1+2*A*(H+(n+1)*A+1))+n*(1+2*A*(H+(n+1)*A+1)) :=
          Nat.add_le_add (ht₁.trans hcommon) ht₂
        _=(n+1)*(1+2*A*(H+(n+1)*A+1)) := by ring
    · rw [run_add,he₁,he₂]
end MatchingFPRAS.StackCost

end OAI
