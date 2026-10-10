import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.CoinAlphabet
import OAI.Combinatorics.MatchingCount.Tapes.CoinStack

namespace OAI

namespace MatchingFPRAS.CoinAlphabet
open Turing
open scoped Classical

variable {Γ Λ σ : Type} [Inhabited Γ] [Fintype Γ]
omit [Inhabited Γ] in
lemma normal_not_writes (l : Λ) (q : TM1.Stmt Γ Λ σ) : TM1to1.Λ'.normal l∉TM1to1.writes q := by
  induction q <;> simp_all [TM1to1.writes]
omit [Inhabited Γ] in
lemma normal_mem (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (l : Λ) :
    TM1to1.Λ'.normal l∈TM1to1.trSupp M S ↔ l∈S := by
  simp only [TM1to1.trSupp,Finset.mem_biUnion,Finset.mem_insert,TM1to1.Λ'.normal.injEq,
    normal_not_writes,or_false]
  constructor
  · rintro ⟨l',hl',rfl⟩; exact hl'
  · intro hl; exact ⟨l,hl,rfl⟩
omit [Inhabited Γ] in
lemma coins_supported (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (c : CoinTM1.Coins Λ)
    (hc : ∀ l∈S,∀ f,c l=some f→∀ b,f b∈S) :
    ∀ l∈TM1to1.trSupp M S,∀ f,coins c l=some f→∀ b,f b∈TM1to1.trSupp M S := by
  intro l hl f hf b
  cases l with
  | normal l =>
    have hl':= (normal_mem M S l).mp hl
    simp only [coins,Option.map_eq_some_iff] at hf
    obtain ⟨g,hg,rfl⟩:=hf
    exact (normal_mem M S (g b)).mpr (hc l hl' g hg b)
  | write a q => simp [coins] at hf
lemma cfg_supported (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    {n : ℕ} (enc : Γ → List.Vector Bool n) (enc0 : enc default=List.Vector.replicate n false)
    (c : TM1.Cfg Γ Λ σ) (hc : c.l∈S.insertNone) :
    (TM1to1.trCfg enc enc0 c).l∈(TM1to1.trSupp M S).insertNone := by
  rcases c with ⟨l,v,T⟩
  cases l with
  | none => simp [TM1to1.trCfg]
  | some l => simpa only [TM1to1.trCfg,Option.map_some,Finset.some_mem_insertNone,normal_mem] using hc
end MatchingFPRAS.CoinAlphabet

namespace MatchingFPRAS.CoinStack
open Turing TM2to1
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]
omit [DecidableEq K] in
lemma normal_not_internal (l : Λ) (q : TM2.Stmt Γ Λ σ) : Λ'.normal l∉trStmts₁ q := by
  induction q using stmtStRec with
  | run k o q ih => simp_all [trStmts₁_run]
  | load f q ih => exact ih
  | branch f q r ihq ihr => simp_all [trStmts₁]
  | goto f => simp [trStmts₁]
  | halt => simp [trStmts₁]
omit [DecidableEq K] in
lemma normal_mem (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ) (l : Λ) :
    Λ'.normal l∈trSupp M S ↔ l∈S := by
  simp only [trSupp,Finset.mem_biUnion,Finset.mem_insert,Λ'.normal.injEq,
    normal_not_internal,or_false]
  constructor
  · rintro ⟨l',hl',rfl⟩; exact hl'
  · intro hl; exact ⟨l,hl,rfl⟩
omit [DecidableEq K] in
lemma coins_supported (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ) (c : CoinTM1.Coins Λ)
    (hc : ∀ l∈S,∀ f,c l=some f→∀ b,f b∈S) :
    ∀ l∈trSupp M S,∀ f,coins c l=some f→∀ b,f b∈trSupp M S := by
  intro l hl f hf b
  cases l with
  | normal l =>
    have hl':= (normal_mem M S l).mp hl
    simp only [coins,Option.map_eq_some_iff] at hf
    obtain ⟨g,hg,rfl⟩:=hf
    exact (normal_mem M S (g b)).mpr (hc l hl' g hg b)
  | go k o q => simp [coins] at hf
  | ret q => simp [coins] at hf
omit [DecidableEq K] in
lemma cfg_supported (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ)
    {c : TM2.Cfg Γ Λ σ} {a : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ}
    (hca : TrCfg c a) (hc : c.l∈S.insertNone) : a.l∈(trSupp M S).insertNone := by
  rcases hca with ⟨L,hL⟩
  rename_i l v S'
  cases l with
  | none => simp
  | some l => simpa only [Option.map_some,Finset.some_mem_insertNone,normal_mem] using hc
end MatchingFPRAS.CoinStack

end OAI
