import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.PivotAlphabetCost
import OAI.Combinatorics.SharpRamsey.Trees.ChronologicalExecution
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedOverhead

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder FreshExecution ExecutedPotential
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I Ω : Type*} [Fintype I] [Fintype Ω]
  {n : ℕ} {b τ P H : ℝ}

def Book.publicAlphabet (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))
    (z : I→Banks (K:=K) (V:=V) b) (U : ChronoDomains (K:=K) (V:=V)) :
    Finset (I×Code (K:=K) (V:=V) b) :=
  univ.biUnion (fun i=>(book.allowed (z i).1 U.swap).image (fun c=>(i,c)))

variable (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))

omit [Finite K] in
lemma Book.mem_publicAlphabet (z : I→Banks (K:=K) (V:=V) b)
    (U : ChronoDomains (K:=K) (V:=V)) (i : I) (c : Code (K:=K) (V:=V) b)
    (hc : c∈book.allowed (z i).1 U.swap) : (i,c)∈book.publicAlphabet z U := by
  exact mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr ⟨c,hc,rfl⟩⟩

omit [Finite K] in
lemma Book.publicAlphabet_card (z : I→Banks (K:=K) (V:=V) b)
    (U : ChronoDomains (K:=K) (V:=V)) :
    (book.publicAlphabet z U).card≤∑ i,(book.allowed (z i).1 U.swap).card := by
  apply (card_biUnion_le).trans
  exact sum_le_sum (fun i _=>card_image_le)

variable (hb : 0≤b) (hH : 0≤H) (hP : 4≤P) (haP : b+log 1000000≤P)
include hb hH hP haP

lemma Book.publicAlphabet_log (z : I→Banks (K:=K) (V:=V) b)
    (U : ChronoDomains (K:=K) (V:=V)) :
    log ((book.publicAlphabet z U).card:ℝ)≤
      log ((Fintype.card I:ℝ)+1)+headerCost (K:=K) (V:=V)+
      (2*(H+22)*(Nat.card K:ℝ)*P)*(potential ((Nat.card K:ℝ)^(n+3)) U+P) := by
  let L := headerCost (K:=K) (V:=V)+
      (2*(H+22)*(Nat.card K:ℝ)*P)*(potential ((Nat.card K:ℝ)^(n+3)) U+P)
  have hL : 0≤L := add_nonneg headerCost_nonneg
    (mul_nonneg (by positivity) (add_nonneg (potential_nonneg _ _) (by linarith)))
  have hs : potential ((Nat.card K:ℝ)^(n+3)) U.swap=potential ((Nat.card K:ℝ)^(n+3)) U := by
    dsimp only [potential,Prod.swap]; rw [mul_comm]
  have hc : ((book.publicAlphabet z U).card:ℝ)≤((Fintype.card I:ℝ)+1)*exp L := by
    calc
      _ ≤ ∑ i,((book.allowed (z i).1 U.swap).card:ℝ) := by exact_mod_cast book.publicAlphabet_card z U
      _ ≤ ∑ _i : I,exp L := by
        apply sum_le_sum
        intro i _
        simpa only [hs] using book.allowed_card_exp hb hH hP haP (z i).1 U.swap
      _ = (Fintype.card I:ℝ)*exp L := by simp only [sum_const,card_univ,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (exp_pos L).le
  by_cases hz : (book.publicAlphabet z U).card=0
  · rw [hz,Nat.cast_zero,log_zero,add_assoc]
    exact add_nonneg (log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) (Fintype.card I); linarith)) hL
  · apply (log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero hz)).mpr
    rw [add_assoc,exp_add,exp_log (by positivity)]
    exact hc

local instance publicCodeDecidableEq : DecidableEq (I×Code (K:=K) (V:=V) b) := Classical.decEq _

variable (hdim : Module.finrank K V=n+3) (hτ : 0≤τ) (hτsmall : τ≤1/40000)

theorem Book.actual_full_entropy (p : Selection.Law Ω)
    (s : Ω→I→Original (K:=K) (V:=V) n b) (z : I→Banks (K:=K) (V:=V) b)
    (t : Ω→BinaryTree I) (U : ChronoDomains (K:=K) (V:=V))
    (N ht m : ℕ) (targets : Ω→I→List (Projectivization K (Module.Dual K V)×Projectivization K V))
    (counts : Ω→I→ℕ) (hcounts : ∀ ω i,counts ω i ≤ m)
    (hN : ∀ ω,(t ω).numNodes≤N) (hht : ∀ ω,(t ω).height≤ht) :
    let rd := fixedRead (fun _i : I=>chronoRead (K:=K) (V:=V) b) z
    let ch := fun ω=>fixedChoose (fun i=>book.chronoChoose hdim hτ hτsmall (s ω i)) z
    let M := fun ω=>codeTree (countReader rd)
      (countChoose (fun y x=>SharpLogRamsey.Incidence.Incident x y) rd (ch ω) (targets ω) (counts ω)) (t ω) U
    let S := univ.image M
    let msg : Ω→S := fun ω=>⟨M ω,mem_image.mpr ⟨ω,mem_univ _,rfl⟩⟩
    Selection.entropy (p.map msg)≤((2*N+1:ℕ):ℝ)*log 2+
      (N:ℝ)*(log ((Fintype.card I:ℝ)+1)+headerCost (K:=K) (V:=V)+log (m+1:ℕ))+
      (2*(H+22)*(Nat.card K:ℝ)*P)*
      ((ht:ℝ)*(potential ((Nat.card K:ℝ)^(n+3)) U+(N:ℝ)*(b+log 4+2*log 2000))+(N:ℝ)*P) := by
  apply full_execution_entropy_overhead p ((Nat.card K:ℝ)^(n+3)) 2000 b
    (2*(H+22)*(Nat.card K:ℝ)*P) P (log ((Fintype.card I:ℝ)+1)+headerCost (K:=K) (V:=V))
    (by have : 0<Nat.card K:=Nat.zero_lt_one.trans (Finite.one_lt_card (α:=K)); positivity)
    (by norm_num) hb (by positivity) (by linarith)
    (add_nonneg (log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) (Fintype.card I); linarith)) headerCost_nonneg)
    N ht m _ (book.publicAlphabet z) _ _ t U targets counts hcounts hN hht
  · intro ω i U c hc
    obtain ⟨x,hx,rfl⟩:=Option.map_eq_some_iff.mp hc
    apply book.mem_publicAlphabet
    exact book.choose_allowed hdim hτ hτsmall (s ω i) (z i) U.swap x hx
  · intro ω i U c hc
    obtain ⟨x,hx,rfl⟩:=Option.map_eq_some_iff.mp hc
    have hh:=book.choose_caps hdim hτ hτsmall (s ω i) U.swap (z i) x hx
    refine ⟨(s ω i).B,(s ω i).A,(s ω i).nonemptyB,(s ω i).nonemptyA,hh.2.1,hh.1,?_,hh.2.2.2.2.2,hh.2.2.2.2.1⟩
    simpa only [mul_comm] using (s ω i).product
  · intro ω i U c hc
    exact book.publicAlphabet_log hb hH hP haP z U

end
end SharpLogRamsey.ActualPivot

end

end OAI
