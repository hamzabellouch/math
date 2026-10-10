import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.ClassSelection

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {α β γ κ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype κ]

def eventPreimage (f : α→β) (E : Finset β) : Finset α :=
  Finset.univ.filter fun a=>f a∈E

omit [Fintype β] in
lemma mem_eventPreimage (f : α→β) (E : Finset β) (a : α) :
    a∈eventPreimage f E ↔ f a∈E := by
  simp only [eventPreimage,Finset.mem_filter,Finset.mem_univ,true_and]

lemma eventMass_map_preimage (p : Law α) (f : α→β) (E : Finset β) :
    eventMass (map p f) E=eventMass p (eventPreimage f E) := by
  have hm:=mean_map p f (fun b=>if b∈E then 1 else 0)
  simpa only [mean,mul_ite,mul_one,mul_zero,eventMass,eventPreimage,Finset.sum_filter,
    Finset.sum_ite_mem,Finset.univ_inter] using hm

lemma conditionOn_mean_exact (p : Law α) (E : Finset α) (h : 0<eventMass p E)
    (f : α→ℝ) : mean (conditionOn p E h) f=
      mean p (fun a=>if a∈E then f a else 0)/eventMass p E := by
  simp only [mean,Finset.sum_div,conditionOn_apply]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a∈E <;> simp only [ha,ite_true,ite_false,mul_zero,zero_mul,zero_div,
    div_mul_eq_mul_div]

lemma map_condition_pullback (p : Law α) (f : α→β) (E : Finset β)
    (h : 0<eventMass (map p f) E) :
    map (conditionOn p (eventPreimage f E) (by rwa [←eventMass_map_preimage])) f=
      conditionOn (map p f) E h := by
  apply Law.ext_mean
  intro g
  rw [mean_map,conditionOn_mean_exact,conditionOn_mean_exact,mean_map]
  congr 1
  · apply mean_congr
    intro a
    simp only [eventPreimage,Finset.mem_filter,Finset.mem_univ,true_and]
  · exact (eventMass_map_preimage p f E).symm

lemma conditionContext_eq_pullback (p : Law (κ×α)) (E : Finset κ)
    (h : 0<eventMass (first p) E) :
    conditionContext p E h=
      conditionOn p (eventPreimage Prod.fst E) (by rwa [←eventMass_map_preimage,map_first]) := by
  apply Law.ext
  funext z
  simp only [conditionContext,adaptiveLaw,conditionOn_apply,eventPreimage,
    Finset.mem_filter,Finset.mem_univ,true_and]
  have he:=eventMass_map_preimage p Prod.fst E
  dsimp only [eventPreimage] at he
  rw [←he,map_first]
  split_ifs
  · rw [div_mul_eq_mul_div,←mass_eq_first_mul_fiber]
  · simp only [zero_mul]

lemma withMessage_pair (p : Law α) (c : α→κ) (x : α→β) (M : β→γ) :
    withMessage (pair p c x) M=pair p (fun a=>(c a,M (x a))) x := by
  rw [withMessage,pair,map_comp]
  rfl
end

open scoped Classical BigOperators
variable {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ]

lemma conditionContext_pair (p : Law α) (c : α→κ) (x : α→β) (E : Finset κ)
    (h : 0<eventMass (map p c) E) :
    pair (conditionOn p (eventPreimage c E) (by rwa [←eventMass_map_preimage])) c x=
      conditionContext (pair p c x) E (by simpa only [first_pair] using h) := by
  have hmass : eventMass (pair p c x) (eventPreimage Prod.fst E)=eventMass (map p c) E := by
    rw [←eventMass_map_preimage,map_first,first_pair]
  have he : eventPreimage (fun a=>(c a,x a)) (eventPreimage Prod.fst E)=eventPreimage c E := by
    ext a
    simp only [eventPreimage,Finset.mem_filter,Finset.mem_univ,true_and]
  have hh:=map_condition_pullback p (fun a=>(c a,x a)) (eventPreimage Prod.fst E)
    (by change 0<eventMass (pair p c x) (eventPreimage Prod.fst E); rwa [hmass])
  simp only [he] at hh
  rw [conditionContext_eq_pullback]
  exact hh

lemma selected_pair (p : Law α) (c : α→κ) {I J : Type*} [Fintype I] [Fintype J]
    (x : α→I→β) (f : κ→J→I) :
    selectByContext (pair p c x) f=pair p c (fun a=>x a ∘ f (c a)) := by
  rw [selectByContext,pair,map_comp]
  rfl
end SharpRamseyFive.FiniteEntropy

end

end OAI
