import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.GuardMachineBase

namespace OAI

namespace MatchingFPRAS.AlphabetCost
open Turing Turing.TM1 Turing.TM1to1 MachineCost

variable {Γ Λ σ : Type*} [Inhabited Γ]

def writesCount : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q => writesCount q
  | .write _ q => writesCount q+1
  | .load _ q => writesCount q
  | .branch _ q r => max (writesCount q) (writesCount r)
  | .goto _ => 0
  | .halt => 0
variable {n : ℕ} (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ)
  (enc0 : enc default = List.Vector.replicate n false)
  (encdec : ∀ a,dec (enc a)=a) (M : Λ → TM1.Stmt Γ Λ σ)
include encdec

theorem statement_time (q : TM1.Stmt Γ Λ σ) (v : σ) (L R : ListBlank Γ) :
    ∃ t : ℕ, t≤writesCount q ∧
      MachineCost.run (TM1.step (tr enc dec M)) t
        (stepAux (trNormal dec q) v (trTape' enc0 L R)) =
        trCfg enc enc0 (stepAux q v (Tape.mk' L R)) := by
  induction q generalizing v L R with
  | move d q ih =>
    cases d <;>
      simp only [trNormal,stepAux_move,stepAux,Tape.move_left_mk',
        trTape'_move_left enc0,trTape'_move_right enc0,writesCount] <;>
      apply ih
  | write f q ih =>
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,writesCount]
    obtain ⟨a,R,rfl⟩:=R.exists_cons
    obtain ⟨t,ht,he⟩:=ih v L (R.cons (f a v))
    refine ⟨t+1,by omega,?_⟩
    rw [MachineCost.run]
    simp only [advance,TM1.step,tr,Option.getD_some,Tape.mk'_head,
      ListBlank.head_cons]
    rw [stepAux_write enc0,stepAux_move,trTape'_move_left enc0]
    simpa using he
  | load f q ih =>
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,writesCount]
    exact ih _ _ _
  | branch p q r ihq ihr =>
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,Tape.mk'_head,writesCount]
    cases h:p R.head v
    · simp only [Bool.cond_false]
      obtain ⟨t,ht,he⟩:=ihr v L R
      exact ⟨t,ht.trans (le_max_right _ _),he⟩
    · simp only [Bool.cond_true]
      obtain ⟨t,ht,he⟩:=ihq v L R
      exact ⟨t,ht.trans (le_max_left _ _),he⟩
  | goto l =>
    refine ⟨0,le_rfl,?_⟩
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,trCfg,trTape_mk',
      MachineCost.run,Tape.mk'_head,Option.map_some]
  | halt =>
    refine ⟨0,le_rfl,?_⟩
    simp only [trNormal,stepAux,trCfg,trTape_mk',MachineCost.run,Option.map_none]

lemma one_step_time (W : ℕ) (hW : ∀ l,writesCount (M l)≤W) (c : TM1.Cfg Γ Λ σ) :
    ∃ t : ℕ,t≤W+1 ∧
      MachineCost.run (TM1.step (tr enc dec M)) t (trCfg enc enc0 c)=
      trCfg enc enc0 (advance (TM1.step M) c) := by
  rcases c with ⟨l,v,T⟩
  obtain ⟨L,R,rfl⟩:=T.exists_mk'
  cases l with
  | none => exact ⟨0,Nat.zero_le _,rfl⟩
  | some l =>
    obtain ⟨t,ht,he⟩:=statement_time enc dec enc0 encdec M (M l) v L R
    refine ⟨t+1,by have:=hW l;omega,?_⟩
    simpa only [MachineCost.run,advance,TM1.step,Option.map_some,trCfg,tr,
      Option.getD_some,trTape_mk'] using he

theorem execution_time (W : ℕ) (hW : ∀ l,writesCount (M l)≤W)
    (c : TM1.Cfg Γ Λ σ) (k : ℕ) :
    ∃ t : ℕ,t≤k*(W+1) ∧
      MachineCost.run (TM1.step (tr enc dec M)) t (trCfg enc enc0 c)=
      trCfg enc enc0 (MachineCost.run (TM1.step M) k c) := by
  induction k generalizing c with
  | zero => exact ⟨0,by simp,rfl⟩
  | succ k ih =>
    obtain ⟨t₁,ht₁,he₁⟩:=one_step_time enc dec enc0 encdec M W hW c
    obtain ⟨t₂,ht₂,he₂⟩:=ih (advance (TM1.step M) c)
    refine ⟨t₁+t₂,?_,?_⟩
    · calc
        t₁+t₂≤(W+1)+k*(W+1) := Nat.add_le_add ht₁ ht₂
        _=(k+1)*(W+1) := by ring
    · rw [run_add,he₁,he₂]; rfl
end MatchingFPRAS.AlphabetCost

end OAI
