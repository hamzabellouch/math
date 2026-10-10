import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.SequentialLaw

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def optionCompose (p : Law (Option α)) (next : Option α→Law (Option β)) :
    Law (Option β) :=
  map (adaptiveLaw p next) (fun ab=>ab.1.bind (fun _=>ab.2))

lemma optionCompose_failure (p : Law (Option α)) (next : Option α→Law (Option β))
    (ε₁ ε₂ : ℝ) (hε₂ : 0≤ε₂) (hp : p none≤ε₁)
    (hn : ∀a,0<p (some a)→next (some a) none≤ε₂) :
    optionCompose p next none≤ε₁+ε₂ := by
  have he : optionCompose p next none=eventMass (adaptiveLaw p next)
      (Finset.univ.filter fun ab=>ab.1=none ∨ ab.2=none) := by
    unfold optionCompose map eventMass
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ab _
    rcases ab with ⟨a,b⟩
    cases a <;> cases b <;> simp
  rw [he]
  exact adaptive_option_failure p next ε₁ ε₂ hε₂ hp hn

lemma optionCompose_positive (p : Law (Option α)) (next : Option α→Law (Option β))
    (b : β) (hb : 0<optionCompose p next (some b)) :
    ∃a,0<p (some a) ∧ 0<next (some a) (some b) := by
  obtain ⟨⟨a,b'⟩,hab,he⟩ := map_positive (adaptiveLaw p next) _ _ hb
  cases a with
  | none => simp at he
  | some a =>
    have he' : b'=some b := by simpa using he
    subst b'
    change 0<p (some a)*next (some a) (some b) at hab
    rcases mul_pos_iff.mp hab with h | h
    · exact ⟨a,h⟩
    · exact False.elim ((not_lt_of_ge (p.nonneg _)) h.1)

end SharpRamseyFive.FiniteEntropy

end OAI
