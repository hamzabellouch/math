import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.SupportedCompiler
import OAI.Combinatorics.MatchingCount.Machines.BoolPostCompiler

namespace OAI

namespace MatchingFPRAS.FixedAlphabetCompiler
open Turing MachineCost
open scoped Classical

variable {Γ Λ σ : Type*} [Inhabited Γ] [Fintype Γ] [Inhabited Λ]
  [Inhabited σ] [Fintype σ]
variable {w : ℕ} (enc : Γ → List.Vector Bool w) (dec : List.Vector Bool w → Γ)
  (enc0 : enc default = List.Vector.replicate w false)
  (encdec : ∀ a,dec (enc a)=a) (M : Λ → TM1.Stmt Γ Λ σ)
  (S : Finset Λ) (hS : TM1.Supports M S)
def bitsWord (input : List Γ) : List Bool := input.flatMap (fun a=>(enc a).toList)
def word (input : List Γ) : List Symbol := (bitsWord enc input).map BoolPostCompiler.up
omit [Fintype Γ] [Fintype σ] in
lemma initial_block (input : List Γ) :
    TM1to1.trCfg enc enc0 (TM1.init (Λ:=Λ) (σ:=σ) input)=
      TM1.init (bitsWord enc input) := by
  simp only [TM1to1.trCfg,TM1.init,Option.map_some,TM1to1.trTape,TM1to1.trTape',
    Tape.mk₁,Tape.mk₂,Tape.mk'_left,Tape.mk'_right₀,ListBlank.flatMap_mk,
    List.flatMap_nil,bitsWord]
  rfl
omit [Fintype Γ] [Fintype σ] [Inhabited Λ] [Inhabited σ] in
lemma output_block (c : TM1.Cfg Γ Λ σ) (output : List Γ)
    (h : c.Tape.right₀=ListBlank.mk output) :
    (TM1to1.trCfg enc enc0 c).Tape.right₀=ListBlank.mk (bitsWord enc output) := by
  change (TM1to1.trTape enc0 c.Tape).right₀=_
  simp only [TM1to1.trTape,TM1to1.trTape',Tape.mk'_right₀,h,ListBlank.flatMap_mk,bitsWord]
noncomputable def support := TM1to1.trSupp M S
include hS in
omit [Inhabited Γ] [Inhabited σ] [Fintype σ] in
lemma block_support : TM1.Supports (TM1to1.tr enc dec M) (support M S) :=
  TM1to1.tr_supports enc dec M hS
noncomputable def compiled : RandomMachine :=
  BoolPostCompiler.compiled (TM1to0.tr (TM1to1.tr enc dec M))
    (TM1to0.trStmts (TM1to1.tr enc dec M) (support M S))
    (TM1to0.tr_supports _ (block_support enc dec M S hS))
noncomputable def cost : ℕ :=
  SupportedCompiler.cost (TM1to1.tr enc dec M) (support M S) *
    (AlphabetCost.supportedWrites M S+1)
include encdec enc0

theorem compiled_words (input output : List Γ) (n t : ℕ)
    (hhalt : (MachineCost.run (TM1.step M) n (TM1.init input)).l=none)
    (hout : (MachineCost.run (TM1.step M) n (TM1.init input)).Tape.right₀=
      ListBlank.mk output)
    (ht : cost enc dec M S*n+2 ≤ t) (bits : Fin t → Bool) :
    (MatchingFPRAS.run (compiled enc dec M S hS) (word enc input) bits).state=none ∧
      (MatchingFPRAS.run (compiled enc dec M S hS) (word enc input) bits).tape.right₀=
        ListBlank.mk (word enc output) := by
  have hi : (TM1.init (Λ:=Λ) (σ:=σ) input).l ∈ S.insertNone :=
    Finset.some_mem_insertNone.mpr hS.1
  obtain ⟨b,hb,he⟩:=AlphabetCost.execution_supported enc dec enc0 encdec M S hS hi n
  rw [initial_block] at he
  have hS' := block_support enc dec M S hS
  have hi' : (TM1.init (Λ:=TM1to1.Λ' Γ Λ σ) (σ:=σ) (bitsWord enc input)).l ∈
      (support M S).insertNone := Finset.some_mem_insertNone.mpr hS'.1
  obtain ⟨k,hk,hke⟩:=SupportedCompiler.post_time (TM1to1.tr enc dec M) (support M S) hS' hi' b
  have initpost : TM1to0.trCfg (TM1to1.tr enc dec M)
      (TM1.init (bitsWord enc input))=TM0.init (bitsWord enc input) := rfl
  rw [initpost,he] at hke
  have hh : TM0.step (TM1to0.tr (TM1to1.tr enc dec M))
      (MachineCost.run (TM0.step (TM1to0.tr (TM1to1.tr enc dec M))) k
        (TM0.init (bitsWord enc input)))=none := by
    rw [hke]
    generalize hc:MachineCost.run (TM1.step M) n (TM1.init input)=c at hhalt ⊢
    rcases c with ⟨l,v,T⟩
    change l=none at hhalt
    subst l
    rfl
  have ho : (MachineCost.run (TM0.step (TM1to0.tr (TM1to1.tr enc dec M))) k
      (TM0.init (bitsWord enc input))).Tape.right₀=ListBlank.mk (bitsWord enc output) := by
    rw [hke]
    exact output_block enc enc0 _ output hout
  have hkt : k+2 ≤ t := by
    apply (Nat.add_le_add_right (hk.trans (Nat.mul_le_mul_left _ hb)) 2).trans
    have hp : SupportedCompiler.cost (TM1to1.tr enc dec M) (support M S) *
        (n*(AlphabetCost.supportedWrites M S+1))+2 = cost enc dec M S*n+2 := by
      unfold cost
      ring
    rw [hp]
    exact ht
  exact BoolPostCompiler.compiled_words _ _ _ (bitsWord enc input) (bitsWord enc output)
    k t hh ho hkt bits
end MatchingFPRAS.FixedAlphabetCompiler

end OAI
