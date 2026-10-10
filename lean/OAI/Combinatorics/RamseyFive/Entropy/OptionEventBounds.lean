import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.LocalNodeLaw

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
lemma pairOptions_event_left (p : Law (Option α×Option β)) (P : Option α→Prop) (hn : ¬P none) :
    eventMass (map p pairOptions) (Finset.univ.filter fun z=>P (z.map Prod.fst))≤
      eventMass p (Finset.univ.filter fun z=>P z.1) := by
  rw [eventMass_map_filter]
  apply eventMass_filter_mono
  rintro ⟨a,b⟩ hp
  cases a <;> cases b <;> simp_all [pairOptions]

lemma pairOptions_event_right (p : Law (Option α×Option β)) (P : Option β→Prop) (hn : ¬P none) :
    eventMass (map p pairOptions) (Finset.univ.filter fun z=>P (z.map Prod.snd))≤
      eventMass p (Finset.univ.filter fun z=>P z.2) := by
  rw [eventMass_map_filter]
  apply eventMass_filter_mono
  rintro ⟨a,b⟩ hp
  cases a <;> cases b <;> simp_all [pairOptions]

lemma optionCompose_event_le (p : Law (Option α)) (next : Option α→Law (Option β))
    (P : Option β→Prop) (hn : ¬P none) (B : ℝ) (hB : 0≤B)
    (h : ∀a,0<p (some a)→eventMass (next (some a)) (Finset.univ.filter P)≤B) :
    eventMass (optionCompose p next) (Finset.univ.filter P)≤B := by
  have he : eventMass (optionCompose p next) (Finset.univ.filter P)=
      ∑a,p a*eventMass (next a) (Finset.univ.filter fun b=>P (a.bind fun _=>b)) := by
    rw [optionCompose,eventMass_map_filter]
    simp only [eventMass,Finset.sum_filter,Fintype.sum_prod_type,adaptiveLaw,
      Finset.mul_sum,mul_ite,mul_zero]
  rw [he]
  calc
    _≤∑a,p a*B := by
      apply Finset.sum_le_sum
      intro a _
      by_cases hz : p a=0
      · simp only [hz,zero_mul,le_refl]
      apply mul_le_mul_of_nonneg_left _ (p.nonneg a)
      cases a with
      | none => simpa [eventMass,hn] using hB
      | some a => exact h a (lt_of_le_of_ne (p.nonneg _) (Ne.symm hz))
    _=B := by rw [←Finset.sum_mul,p.sum_one,one_mul]
end SharpRamseyFive.FiniteEntropy

end OAI
