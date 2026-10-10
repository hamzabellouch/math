import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.OptionComposition

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
lemma map_const (p : Law α) (b : β) : map p (fun _=>b)=pureLaw b := by
  apply Law.ext
  funext x
  by_cases hx : b=x
  · subst x
    simp [map,pureLaw,p.sum_one]
  · simp [map,pureLaw,hx,Ne.symm hx]

lemma adaptive_output_mass (p : Law α) (next : α→Law β) (out : α→β→γ) (c : γ) :
    map (adaptiveLaw p next) (fun z=>out z.1 z.2) c=
      ∑a,p a*map (next a) (out a) c := by
  simp only [map,adaptiveLaw,Fintype.sum_prod_type,Finset.mul_sum,mul_ite,mul_zero]

lemma public_composition (p : Law α) (tape : Law β) (firstOut : α→γ)
    (out : γ→β→δ) (next : γ→Law δ)
    (hm : ∀c,map tape (out c)=next c) :
    map (adaptiveLaw p (fun _=>tape)) (fun z=>out (firstOut z.1) z.2)=
      map (adaptiveLaw (map p firstOut) next) Prod.snd := by
  apply Law.ext
  funext d
  rw [adaptive_output_mass (out:=fun a b=>out (firstOut a) b)]
  have hr := adaptive_output_mass (map p firstOut) next (fun _ x=>x) d
  change map (adaptiveLaw (map p firstOut) next) Prod.snd d = ∑ a, map p firstOut a * map (next a) id d at hr
  simp only [map_id] at hr
  rw [hr,sum_map]
  apply Finset.sum_congr rfl
  intro a _
  rw [hm]

lemma optionCompose_eq_second (p : Law (Option α))
    (next : Option α→Law (Option β)) (hn : next none=pureLaw none) :
    optionCompose p next=map (adaptiveLaw p next) Prod.snd := by
  apply Law.ext
  funext b
  have h₁ := adaptive_output_mass p next (fun a b=>a.bind fun _=>b) b
  have h₂ := adaptive_output_mass p next (fun _ b=>b) b
  rw [optionCompose,h₁,h₂]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  cases a with
  | none =>
    change map (next none) (fun _ : Option β => (none : Option β)) b = map (next none) id b
    rw [map_const,map_id,hn]
  | some a => rfl
end SharpRamseyFive.FiniteEntropy

end OAI
