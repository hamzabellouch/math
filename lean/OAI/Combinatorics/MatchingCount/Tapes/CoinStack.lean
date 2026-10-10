import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.StackCompilerCost
import OAI.Combinatorics.MatchingCount.Graphs.SafeTrace

namespace OAI

namespace MatchingFPRAS.CoinStack
open Turing TM2to1 TM2to1.Λ' MachineCost StackCost SafeTrace

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]

def safe (p : Λ → Prop) : Λ' K Γ Λ σ → Prop
  | .normal l => p l
  | .go _ _ _ | .ret _ => True

def coins (c : CoinTM1.Coins Λ) : CoinTM1.Coins (Λ' K Γ Λ σ)
  | .normal l => (c l).map (fun f b=>.normal (f b))
  | .go _ _ _ | .ret _ => none

variable (M : Λ → TM2.Stmt Γ Λ σ) (p : Λ → Prop)
lemma go_path {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    {S : List (Γ k)} {L : ListBlank (∀ k,Option (Γ k))}
    (hL : L.map (proj k)=ListBlank.mk (S.map some).reverse)
    (n : ℕ) (hn : n≤ S.length) :
    Path (tr M) (safe p) n ⟨some (go k o q),v,Tape.mk' ∅ (addBottom L)⟩
      ⟨some (go k o q),v,(Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  rw [←go_time M o q v hL n hn]
  apply Path.of_run
  intro i hi l hl
  rw [go_time M o q v hL i (by omega)] at hl
  cases hl
  trivial

lemma return_path (q : TM2.Stmt Γ Λ σ) (v : σ) (L : ListBlank (∀ k,Option (Γ k))) (n : ℕ) :
    Path (tr M) (safe p) n
      ⟨some (ret q),v,(Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))⟩
      ⟨some (ret q),v,Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    apply Path.cons (by intro l hl; cases hl; trivial)
    have hs : advance (TM1.step (tr M))
        ⟨some (ret q),v,(Tape.move .right)^[n+1] (Tape.mk' ∅ (addBottom L))⟩=
        ⟨some (ret q),v,(Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
      simp only [advance,TM1.step,tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,
        addBottom_nth_succ_fst,Bool.cond_false]
      rw [Function.iterate_succ_apply',Tape.move_right_left]
      rfl
    rw [hs]
    exact ih

theorem statement_path (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k,List (Γ k))
    (L : ListBlank (∀ k,Option (Γ k))) (H : ℕ) (hS : StackBound S H)
    (hL : ∀ k,L.map (proj k)=ListBlank.mk ((S k).map some).reverse) :
    ∃ (t : ℕ) (b : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ),
      t≤ 2*accesses q*(H+accesses q+1) ∧ TrCfg (TM2.stepAux q v S) b ∧
      Path (tr M) (safe p) t
        (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom L))) b := by
  induction q using stmtStRec generalizing v S L H with
  | run k o q ih =>
    let v':=stVar v (S k) o
    let S':=Function.update S k (stWrite v (S k) o)
    have hS' : StackBound S' (H+1):=action_bound hS o v
    obtain ⟨L',hL',hact⟩:=tr_respects_aux₂
      (q:=TM1.Stmt.goto fun _ _=>ret q) hL o
    obtain ⟨t,b,ht,hb,he⟩:=ih v' S' L' (H+1) hS' hL'
    have hgo:=go_path M p o q v (hL k) (S k).length le_rfl
    have hs : advance (TM1.step (tr M))
        ⟨some (go k o q),v,(Tape.move .right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩=
        ⟨some (ret q),v',(Tape.move .right)^[(S' k).length] (Tape.mk' ∅ (addBottom L'))⟩ := by
      simp only [advance,TM1.step]
      rw [tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,addBottom_nth_snd,
        stk_nth_val _ (hL k),List.getElem?_eq_none (le_of_eq List.length_reverse)]
      simp only [Option.isNone_none,Bool.cond_true]
      rw [hact]
      rfl
    have hstep:=Path.single (M:=tr M) (safe:=safe p)
      (⟨some (go k o q),v,(Tape.move .right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩)
      (by intro l hl; cases hl; trivial)
    rw [hs] at hstep
    have hret:=return_path M p q v' L' (S' k).length
    have hlast:=Path.single (M:=tr M) (safe:=safe p)
      (⟨some (ret q),v',Tape.mk' ∅ (addBottom L')⟩)
      (by intro l hl; cases hl; trivial)
    have hf : advance (TM1.step (tr M)) ⟨some (ret q),v',Tape.mk' ∅ (addBottom L')⟩=
        TM1.stepAux (trNormal q) v' (Tape.mk' ∅ (addBottom L')) := by
      simp only [advance,TM1.step,tr,TM1.stepAux,Tape.mk'_head,addBottom_head_fst,
        Bool.cond_true,Option.getD_some]
    rw [hf] at hlast
    refine ⟨(S k).length+1+(S' k).length+1+t,b,?_,?_,?_⟩
    · rw [accesses_run]
      have h₁:=hS k
      have h₂:=hS' k
      nlinarith
    · simpa only [step_run] using hb
    · simpa only [trNormal_run,TM1.stepAux] using (((hgo.trans hstep).trans hret).trans hlast).trans he
  | load a q ih => exact ih (a v) S L H hS hL
  | branch f q r ihq ihr =>
    cases hp:f v
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
  | goto f => exact ⟨0,_,Nat.zero_le _,⟨L,hL⟩,.refl _⟩
  | halt => exact ⟨0,_,Nat.zero_le _,⟨L,hL⟩,.refl _⟩

lemma one_step_path (A : ℕ) (hA : ∀ l,accesses (M l)≤ A)
    {c : TM2.Cfg Γ Λ σ} {a : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ}
    (hca : TrCfg c a) (hc : ∀ l,c.l=some l→p l) (H : ℕ) (hS : StackBound c.stk H) :
    ∃ (t : ℕ) (b : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ),
      t≤ 1+2*A*(H+A+1) ∧ TrCfg (advance (TM2.step M) c) b ∧ Path (tr M) (safe p) t a b := by
  rcases hca with ⟨L,hL⟩
  rename_i l v S
  cases l with
  | none => exact ⟨0,_,Nat.zero_le _,⟨L,hL⟩,.refl _⟩
  | some l =>
    obtain ⟨t,b,ht,hb,he⟩:=statement_path M p (M l) v S L H hS hL
    refine ⟨t+1,b,?_,hb,?_⟩
    · have hh : 2*accesses (M l)*(H+accesses (M l)+1)≤ 2*A*(H+A+1) := by
        gcongr <;> exact hA l
      omega
    · apply Path.cons (by intro l' hl; cases hl; exact hc l rfl)
      simpa only [advance,TM1.step,Option.map_some,tr,Option.getD_some] using he

omit [DecidableEq K] in
lemma coins_none {c : CoinTM1.Coins Λ} {l : Λ' K Γ Λ σ}
    (h : safe (fun l=>c l=none) l) : coins c l=none := by
  cases l with
  | normal l => simp only [coins,safe] at *; rw [h]; rfl
  | go k o q => rfl
  | ret q => rfl
end MatchingFPRAS.CoinStack

end OAI
