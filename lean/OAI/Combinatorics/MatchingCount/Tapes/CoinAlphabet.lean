import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.SupportedCompiler
import OAI.Combinatorics.MatchingCount.Graphs.SafeTrace

namespace OAI

namespace MatchingFPRAS.CoinAlphabet
open Turing TM1 TM1to1 MachineCost SafeTrace

variable {Γ Λ σ : Type} [Inhabited Γ]
def safe (p : Λ → Prop) : Λ' Γ Λ σ → Prop
  | .normal l => p l
  | .write _ _ => True

def coins (c : CoinTM1.Coins Λ) : CoinTM1.Coins (Λ' Γ Λ σ)
  | .normal l => (c l).map (fun f b=>.normal (f b))
  | .write _ _ => none

variable {n : ℕ} (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ)
  (enc0 : enc default=List.Vector.replicate n false)
  (encdec : ∀ a,dec (enc a)=a) (M : Λ → TM1.Stmt Γ Λ σ)

include encdec

theorem statement_path (p : Λ → Prop) (q : TM1.Stmt Γ Λ σ) (v : σ) (L R : ListBlank Γ) :
    ∃ t,t≤AlphabetCost.writesCount q ∧
      Path (tr enc dec M) (safe p) t
        (stepAux (trNormal dec q) v (trTape' enc0 L R))
        (trCfg enc enc0 (stepAux q v (Tape.mk' L R))) := by
  induction q generalizing v L R with
  | move d q ih =>
    cases d <;>
      simp only [trNormal,stepAux_move,stepAux,Tape.move_left_mk',
        trTape'_move_left enc0,trTape'_move_right enc0,AlphabetCost.writesCount] <;>
      apply ih
  | write f q ih =>
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,AlphabetCost.writesCount]
    obtain ⟨a,R,rfl⟩:=R.exists_cons
    obtain ⟨t,ht,he⟩:=ih v L (R.cons (f a v))
    refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
    apply Path.cons (by intro l hl; cases hl; trivial)
    simp only [advance,TM1.step,tr,Option.getD_some,Tape.mk'_head,ListBlank.head_cons]
    rw [stepAux_write enc0,stepAux_move,trTape'_move_left enc0]
    simpa using he
  | load f q ih =>
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,AlphabetCost.writesCount]
    exact ih _ _ _
  | branch p' q r ihq ihr =>
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,Tape.mk'_head,AlphabetCost.writesCount]
    cases h:p' R.head v
    · simp only [Bool.cond_false]
      obtain ⟨t,ht,he⟩:=ihr v L R
      exact ⟨t,ht.trans (le_max_right _ _),he⟩
    · simp only [Bool.cond_true]
      obtain ⟨t,ht,he⟩:=ihq v L R
      exact ⟨t,ht.trans (le_max_left _ _),he⟩
  | goto f =>
    refine ⟨0,le_rfl,?_⟩
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,trCfg,trTape_mk',Tape.mk'_head,Option.map_some]
    exact .refl _
  | halt =>
    refine ⟨0,le_rfl,?_⟩
    simp only [trNormal,stepAux,trCfg,trTape_mk',Option.map_none]
    exact .refl _

lemma one_step_path (p : Λ → Prop) (c : TM1.Cfg Γ Λ σ) (hc : ∀ l,c.l=some l→p l) :
    ∃ t,t≤(match c.l with | none=>0 | some l=>AlphabetCost.writesCount (M l)+1) ∧
      Path (tr enc dec M) (safe p) t (trCfg enc enc0 c)
        (trCfg enc enc0 (advance (TM1.step M) c)) := by
  rcases c with ⟨l,v,T⟩
  obtain ⟨L,R,rfl⟩:=T.exists_mk'
  cases l with
  | none => exact ⟨0,le_rfl,.refl _⟩
  | some l =>
    obtain ⟨t,ht,he⟩:=statement_path enc dec enc0 encdec M p (M l) v L R
    refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
    apply Path.cons (by intro l' hl; cases hl; exact hc l rfl)
    simpa only [advance,TM1.step,Option.map_some,trCfg,tr,Option.getD_some,trTape_mk'] using he

theorem path_supported [Inhabited Λ] [Inhabited σ] (S : Finset Λ) (hS : TM1.Supports M S)
    {p : Λ → Prop} {k : ℕ} {a b : TM1.Cfg Γ Λ σ}
    (h : Path M p k a b) (ha : a.l∈S.insertNone) :
    ∃ t,t≤k*(AlphabetCost.supportedWrites M S+1) ∧
      Path (tr enc dec M) (safe p) t (trCfg enc enc0 a) (trCfg enc enc0 b) := by
  classical
  induction h with
  | refl a => exact ⟨0,by simp,.refl _⟩
  | @cons k a b hs hr ih =>
    obtain ⟨i,hi,hiP⟩:=one_step_path enc dec enc0 encdec M p a hs
    obtain ⟨j,hj,hjP⟩:=ih (SupportedCompiler.advance_supported M S hS ha)
    have hi' : i≤AlphabetCost.supportedWrites M S+1 := by
      rcases a with ⟨l,v,T⟩
      cases l with
      | none => dsimp at hi; omega
      | some l =>
        have hl:=Finset.some_mem_insertNone.mp ha
        have hw : AlphabetCost.writesCount (M l)≤AlphabetCost.supportedWrites M S :=
          Finset.le_sup (f:=fun l=>AlphabetCost.writesCount (M l)) hl
        dsimp at hi
        omega
    refine ⟨i+j,?_,hiP.trans hjP⟩
    calc i+j≤(AlphabetCost.supportedWrites M S+1)+k*(AlphabetCost.supportedWrites M S+1) := Nat.add_le_add hi' hj
         _=(k+1)*(AlphabetCost.supportedWrites M S+1) := by ring

omit [Inhabited Γ] encdec in
lemma coins_none {c : CoinTM1.Coins Λ} {l : Λ' Γ Λ σ}
    (h : safe (fun l=>c l=none) l) : coins c l=none := by
  cases l with
  | normal l => simp only [coins,safe] at *; rw [h]; rfl
  | write a q => rfl
end MatchingFPRAS.CoinAlphabet

end OAI
