import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.AlphabetCompilerCost

namespace OAI

namespace MatchingFPRAS.SupportedCompiler
open Turing MachineCost
open scoped Classical

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hS : TM1.Supports M S)
noncomputable def cost : ℕ := S.sup (fun l=>statementCost (M l))
omit [Inhabited Γ] [Inhabited Λ] [Inhabited σ] in
lemma cost_le {l : Λ} (hl : l ∈ S) : statementCost (M l) ≤ cost M S := Finset.le_sup (f:=fun l=>statementCost (M l)) hl
include hS
omit [Inhabited σ] in
lemma advance_supported {c : TM1.Cfg Γ Λ σ} (hc : c.l ∈ S.insertNone) :
    (advance (TM1.step M) c).l ∈ S.insertNone := by
  cases he:TM1.step M c with
  | none => simpa only [advance,he,Option.getD_none] using hc
  | some c' =>
    simpa only [advance,he,Option.getD_some] using TM1.step_supports M hS he hc
omit [Inhabited σ] in
lemma run_supported {c : TM1.Cfg Γ Λ σ} (hc : c.l ∈ S.insertNone) (n : ℕ) :
    (MachineCost.run (TM1.step M) n c).l ∈ S.insertNone := by
  induction n generalizing c with
  | zero => exact hc
  | succ n ih => exact ih (advance_supported M S hS hc)

theorem post_time {c : TM1.Cfg Γ Λ σ} (hc : c.l ∈ S.insertNone) (n : ℕ) :
    ∃ k ≤ cost M S*n,
      MachineCost.run (TM0.step (TM1to0.tr M)) k (TM1to0.trCfg M c)=
        TM1to0.trCfg M (MachineCost.run (TM1.step M) n c) := by
  induction n generalizing c with
  | zero => exact ⟨0,by simp,rfl⟩
  | succ n ih =>
    rcases c with ⟨l,v,T⟩
    cases l with
    | none =>
      have he : ∀ j,MachineCost.run (TM1.step M) j ⟨none,v,T⟩=⟨none,v,T⟩ := by
        intro j
        induction j with
        | zero => rfl
        | succ j hj => exact hj
      exact ⟨0,Nat.zero_le _,by rw [MachineCost.run,he]⟩
    | some l =>
      have hl : l ∈ S:=Finset.some_mem_insertNone.mp hc
      obtain ⟨j,hj,hjc,hje⟩:=statement_translation_time M (M l) v T
      have hc' : (TM1.stepAux (M l) v T).l ∈ S.insertNone :=
        advance_supported M S hS hc
      obtain ⟨k,hk,hke⟩:=ih hc'
      refine ⟨j+k,?_,?_⟩
      · have hj' := hjc.trans (cost_le M S hl)
        calc
          j+k ≤ cost M S+cost M S*n:=Nat.add_le_add hj' hk
          _=cost M S*(n+1):=by ring
      · rw [run_add]
        change MachineCost.run (TM0.step (TM1to0.tr M)) k
          (MachineCost.run (TM0.step (TM1to0.tr M)) j ⟨(some (M l),v),T⟩)=_
        rw [hje,hke]
        rfl
end MatchingFPRAS.SupportedCompiler

namespace MatchingFPRAS.AlphabetCost
open Turing MachineCost SupportedCompiler
open scoped Classical

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable {n : ℕ} (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ)
  (enc0 : enc default = List.Vector.replicate n false)
  (encdec : ∀ a,dec (enc a)=a) (M : Λ → TM1.Stmt Γ Λ σ)
  (S : Finset Λ) (hS : TM1.Supports M S)
include encdec hS
noncomputable def supportedWrites : ℕ := S.sup (fun l=>writesCount (M l))
omit [Inhabited σ] hS in
lemma one_step_supported (_hS : TM1.Supports M S) {c : TM1.Cfg Γ Λ σ} (hc : c.l ∈ S.insertNone) :
    ∃ t : ℕ,t ≤ supportedWrites M S+1 ∧
      MachineCost.run (TM1.step (TM1to1.tr enc dec M)) t (TM1to1.trCfg enc enc0 c)=
      TM1to1.trCfg enc enc0 (advance (TM1.step M) c) := by
  rcases c with ⟨l,v,T⟩
  obtain ⟨L,R,rfl⟩:=T.exists_mk'
  cases l with
  | none => exact ⟨0,Nat.zero_le _,rfl⟩
  | some l =>
    obtain ⟨t,ht,he⟩:=statement_time enc dec enc0 encdec M (M l) v L R
    have hh : writesCount (M l) ≤ supportedWrites M S:=
      Finset.le_sup (f:=fun l=>writesCount (M l)) (Finset.some_mem_insertNone.mp hc)
    refine ⟨t+1,by omega,?_⟩
    simpa only [MachineCost.run,advance,TM1.step,Option.map_some,TM1to1.trCfg,TM1to1.tr,
      Option.getD_some,TM1to1.trTape_mk'] using he

omit [Inhabited σ] in
theorem execution_supported {c : TM1.Cfg Γ Λ σ} (hc : c.l ∈ S.insertNone) (k : ℕ) :
    ∃ t : ℕ,t ≤ k*(supportedWrites M S+1) ∧
      MachineCost.run (TM1.step (TM1to1.tr enc dec M)) t (TM1to1.trCfg enc enc0 c)=
      TM1to1.trCfg enc enc0 (MachineCost.run (TM1.step M) k c) := by
  induction k generalizing c with
  | zero => exact ⟨0,by simp,rfl⟩
  | succ k ih =>
    obtain ⟨t₁,ht₁,he₁⟩:=one_step_supported enc dec enc0 encdec M S hS hc
    obtain ⟨t₂,ht₂,he₂⟩:=ih (advance_supported M S hS hc)
    refine ⟨t₁+t₂,?_,?_⟩
    · calc
        t₁+t₂ ≤ (supportedWrites M S+1)+k*(supportedWrites M S+1) := Nat.add_le_add ht₁ ht₂
        _=(k+1)*(supportedWrites M S+1) := by ring
    · rw [run_add,he₁,he₂]; rfl
end MatchingFPRAS.AlphabetCost

end OAI
