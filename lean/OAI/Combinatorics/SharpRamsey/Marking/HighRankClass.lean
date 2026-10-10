import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.HighRankReplacement
import OAI.Combinatorics.SharpRamsey.Marking.ClassTransport

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real ActualHighRank
open scoped Classical BigOperators
noncomputable section

lemma card_first_fiber {A B : Type*} [Fintype A] [Fintype B]
    (S : Finset (A×B)) (a : A) :
    (univ.filter (fun b=>(a,b)∈S)).card=(S.filter (fun z=>z.1=a)).card := by
  apply card_bij (fun b _=>(a,b))
  · intro b hb
    exact mem_filter.mpr ⟨(mem_filter.mp hb).2,rfl⟩
  · intro a ha b hb h
    exact Prod.mk.inj h|>.2
  · intro z hz
    have he : (a,z.2)=z := by ext <;> simp only [(mem_filter.mp hz).2]
    exact ⟨z.2,mem_filter.mpr ⟨mem_univ _,by rw [he]; exact (mem_filter.mp hz).1⟩,he⟩

lemma card_second_fiber {A B : Type*} [Fintype A] [Fintype B]
    (S : Finset (A×B)) (b : B) :
    (univ.filter (fun a=>(a,b)∈S)).card=(S.filter (fun z=>z.2=b)).card := by
  apply card_bij (fun a _=>(a,b))
  · intro a ha
    exact mem_filter.mpr ⟨(mem_filter.mp ha).2,rfl⟩
  · intro a ha b hb h
    exact Prod.mk.inj h|>.1
  · intro z hz
    have he : (z.1,b)=z := by ext <;> simp only [(mem_filter.mp hz).2]
    exact ⟨z.1,mem_filter.mpr ⟨mem_univ _,by rw [he]; exact (mem_filter.mp hz).1⟩,he⟩

variable {K : Type} [Field K] [Fintype K] {d : ℕ}
local instance flat_ActualHighRankClass_1 : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankClass_2 : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankClass_3 : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance flat_ActualHighRankClass_4 : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local instance flat_ActualHighRankClass_5 : Fintype (Projectivization K (Module.Dual K (Module.Dual K (Fin (d+1)→K)))) := Fintype.ofFinite _
local notation "A" => Projectivization K (Module.Dual K (Fin (d+1)→K))
local notation "B" => Projectivization K (Fin (d+1)→K)

theorem covectorDomain_high {gap : ℝ} (S : Finset (B×A)) (r r' : Fin (d+1))
    (h : ValidSlotClass d gap S (.inr (r,r')))
    (hs : (S.card:ℝ)≤64*(Nat.card K:ℝ)^d) :
    2≤r.val ∧ r.val≤d ∧ d+2≤r.val+r'.val ∧
      Caps (log (Nat.card K)) r.val r'.val (covectorDomain S) := by
  obtain ⟨hr,hr',hsum,hA,hB,hfB,hfA⟩:=h
  have hrd : r.val≤d := Nat.le_of_lt_succ r.is_lt
  have hr'd : r'.val≤d := Nat.le_of_lt_succ r'.is_lt
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hexp (m : ℕ) (hm : m≤d) :
      (Nat.card K:ℝ)^(d-m)=exp (((d:ℝ)-m)*log (Nat.card K)) := by
    rw [←Nat.cast_sub hm,exp_nat_mul,exp_log hq]
  refine ⟨by omega,hrd,by omega,?_,?_,?_,?_,?_⟩
  · rw [covectorDomain_first]
    exact hB.trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  · rw [covectorDomain_second]
    exact hA.trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  · rwa [covectorDomain_card]
  · intro a
    have he : univ.filter (fun b=>(a,b)∈covectorDomain S)=univ.filter (fun b=>(b,a)∈S) := by
      ext b
      simp only [mem_filter,mem_univ,true_and]
      exact covectorDomain_mem S (b,a)
    rw [he,card_second_fiber,←hexp r'.val hr'd]
    exact hfA a
  · intro b
    have he : univ.filter (fun a=>(a,b)∈covectorDomain S)=univ.filter (fun a=>(b,a)∈S) := by
      ext a
      simp only [mem_filter,mem_univ,true_and]
      exact covectorDomain_mem S (b,a)
    rw [he,card_first_fiber,←hexp r.val hrd]
    exact hfB b

end
end SharpLogRamsey.Marking

end

end OAI
