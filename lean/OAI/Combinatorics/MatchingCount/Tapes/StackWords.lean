import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.StackCompilerCost
import OAI.Combinatorics.MatchingCount.Tapes.FixedAlphabetCompiler

namespace OAI

namespace MatchingFPRAS.StackWords
open Turing MachineCost

variable {K : Type*} {Γ : K → Type*}
def rows (S : ∀ k,List (Γ k)) (H : ℕ) : List (∀ k,Option (Γ k)) :=
  List.ofFn (fun i : Fin H=>fun k=>(S k).reverse[i.val]?)
def word (S : ∀ k,List (Γ k)) (H : ℕ) : List (TM2to1.Γ' K Γ) :=
  (true,(rows S H).headI)::((rows S H).tail.map (fun a=>(false,a)))
lemma word_length (S : ∀ k,List (Γ k)) (H : ℕ) : (word S H).length ≤ H+1 := by
  change ((rows S H).tail.map (fun a=>(false,a))).length+1 ≤ H+1
  rw [List.length_map,List.length_tail]
  simp only [rows,List.length_ofFn]
  omega
lemma rows_projection (S : ∀ k,List (Γ k)) (H : ℕ) (hS : StackCost.StackBound S H)
    (k : K) : (ListBlank.mk (rows S H)).map (proj k)=ListBlank.mk ((S k).map some).reverse := by
  apply ListBlank.ext
  intro i
  rw [ListBlank.nth_map,ListBlank.nth_mk,List.getI_eq_getElem?_getD]
  simp only [rows,List.getElem?_ofFn,proj,PointedMap.mk_val]
  rw [←List.map_reverse,ListBlank.nth_mk,List.getI_eq_getElem?_getD,List.getElem?_map]
  by_cases hi : i<H
  · simp only [hi,Option.getD_some,dite_true]
    cases (S k).reverse[i]? <;> rfl
  · have hlen : (S k).reverse.length ≤ i := by simpa using (hS k).trans (Nat.le_of_not_gt hi)
    simp [hi,List.getElem?_eq_none hlen]
lemma word_blank (S : ∀ k,List (Γ k)) (H : ℕ) :
    ListBlank.mk (word S H)=TM2to1.addBottom (ListBlank.mk (rows S H)) := by
  simp only [word,TM2to1.addBottom,ListBlank.head_mk,ListBlank.tail_mk,
    ListBlank.map_mk]
  exact (ListBlank.cons_mk _ _).symm
lemma unique_rows (S : ∀ k,List (Γ k)) (H : ℕ) (hS : StackCost.StackBound S H)
    (L : ListBlank (∀ k,Option (Γ k)))
    (hL : ∀ k,L.map (proj k)=ListBlank.mk ((S k).map some).reverse) :
    L=ListBlank.mk (rows S H) := by
  apply ListBlank.ext
  intro i
  funext k
  rw [TM2to1.stk_nth_val i (hL k),TM2to1.stk_nth_val i (rows_projection S H hS k)]
variable {Λ σ : Type*} [Inhabited Λ] [Inhabited σ]
lemma initial (S : ∀ k,List (Γ k)) (H : ℕ) (hS : StackCost.StackBound S H) :
    TM2to1.TrCfg (⟨some default,default,S⟩ : TM2.Cfg Γ Λ σ)
      (TM1.init (word S H)) := by
  have h:=TM2to1.TrCfg.mk (Λ:=Λ) (σ:=σ) (q:=some default) (v:=default)
    (ListBlank.mk (rows S H)) (rows_projection S H hS)
  convert h using 1
  simp only [TM1.init,Tape.mk₁,Tape.mk₂,word_blank]
  rfl
omit [Inhabited Λ] [Inhabited σ] in
lemma output {c : TM2.Cfg Γ Λ σ} {b : TM1.Cfg (TM2to1.Γ' K Γ) (TM2to1.Λ' K Γ Λ σ) σ}
    (hcb : TM2to1.TrCfg c b) (H : ℕ) (hS : StackCost.StackBound c.stk H) :
    b.l=c.l.map TM2to1.Λ'.normal ∧ b.Tape.right₀=ListBlank.mk (word c.stk H) := by
  rcases hcb with ⟨L,hL⟩
  constructor
  · rfl
  · simp only [Tape.mk'_right₀,word_blank]
    rw [unique_rows _ H hS L hL]
variable [DecidableEq K] [Fintype K] [∀ k,Fintype (Γ k)] [Fintype σ]
variable {w : ℕ} (enc : TM2to1.Γ' K Γ → List.Vector Bool w)
  (dec : List.Vector Bool w → TM2to1.Γ' K Γ)
  (enc0 : enc default=List.Vector.replicate w false)
  (encdec : ∀ a,dec (enc a)=a)
  (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ) (hs : TM2.Supports M S)
noncomputable def compiled : RandomMachine :=
  FixedAlphabetCompiler.compiled enc dec (TM2to1.tr M) (TM2to1.trSupp M S)
    (TM2to1.tr_supports M hs)
noncomputable def cost : ℕ :=
  FixedAlphabetCompiler.cost enc dec (TM2to1.tr M) (TM2to1.trSupp M S)
def encoded (S₀ : ∀ k,List (Γ k)) (H : ℕ) : List Symbol :=
  FixedAlphabetCompiler.word enc (word S₀ H)
include enc0 encdec

theorem compiled_execution (A : ℕ) (hA : ∀ l,StackCost.accesses (M l)≤A)
    (S₀ : ∀ k,List (Γ k)) (H₀ : ℕ) (h₀ : StackCost.StackBound S₀ H₀)
    (n H₁ : ℕ)
    (hh : (MachineCost.run (TM2.step M) n ⟨some default,default,S₀⟩).l=none)
    (ho : StackCost.StackBound (MachineCost.run (TM2.step M) n ⟨some default,default,S₀⟩).stk H₁)
    (t : ℕ) (ht : cost enc dec M S*(n*(1+2*A*(H₀+n*A+1)))+2≤t)
    (bits : Fin t → Bool) :
    (MatchingFPRAS.run (compiled enc dec M S hs) (encoded enc S₀ H₀) bits).state=none ∧
    (MatchingFPRAS.run (compiled enc dec M S hs) (encoded enc S₀ H₀) bits).tape.right₀=
      ListBlank.mk (encoded enc (MachineCost.run (TM2.step M) n ⟨some default,default,S₀⟩).stk H₁) := by
  obtain ⟨k,b,hk,hb,he⟩:=StackCost.execution_time M A hA (initial (Λ:=Λ) (σ:=σ) S₀ H₀ h₀) H₀ h₀ n
  have hb' := output hb H₁ ho
  have hhalt : (MachineCost.run (TM1.step (TM2to1.tr M)) k (TM1.init (word S₀ H₀))).l=none := by
    rw [he,hb'.1,hh]
    rfl
  have hout : (MachineCost.run (TM1.step (TM2to1.tr M)) k (TM1.init (word S₀ H₀))).Tape.right₀=
      ListBlank.mk (word (MachineCost.run (TM2.step M) n ⟨some default,default,S₀⟩).stk H₁) := by
    rw [he,hb'.2]
  have htime : FixedAlphabetCompiler.cost enc dec (TM2to1.tr M) (TM2to1.trSupp M S)*k+2≤t :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hk) 2).trans ht
  exact FixedAlphabetCompiler.compiled_words enc dec enc0 encdec (TM2to1.tr M)
    (TM2to1.trSupp M S) (TM2to1.tr_supports M hs) (word S₀ H₀)
    (word (MachineCost.run (TM2.step M) n ⟨some default,default,S₀⟩).stk H₁)
    k t hhalt hout htime bits
end MatchingFPRAS.StackWords

end OAI
