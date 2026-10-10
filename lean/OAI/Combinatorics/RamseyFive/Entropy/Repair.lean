import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.GoodRepresentative

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

lemma Law.exists_positive (p : Law α) : ∃ a,0<p a := by
  by_contra h
  push Not at h
  have hz : ∑ a,p a=0 := Finset.sum_eq_zero (fun a _=>le_antisymm (h a) (p.nonneg a))
  rw [p.sum_one] at hz
  norm_num at hz

def Law.repair (p : Law α) (a : α) : α :=
  if 0<p a then a else Classical.choose p.exists_positive

lemma Law.repair_positive (p : Law α) (a : α) : 0<p (p.repair a) := by
  unfold Law.repair
  split_ifs with h
  · exact h
  · exact Classical.choose_spec p.exists_positive

lemma Law.repair_of_positive (p : Law α) (a : α) (h : 0<p a) : p.repair a=a := by
  simp only [Law.repair,ite_eq_left h]

lemma Law.repair_mean (p : Law α) (f : α→ℝ) :
    (∑ a,p a*f (p.repair a))=∑ a,p a*f a := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : 0<p a
  · rw [p.repair_of_positive a h]
  · rw [show p a=0 from le_antisymm (le_of_not_gt h) (p.nonneg a),zero_mul,zero_mul]

lemma repaired_levels_conditioned_domination (μ : Law (Finset α)) (p : Law α)
    (E : Finset α) (hE : 0<eventMass p E) (C : ℝ) (hC : 0≤C)
    (hsub : ∀ A,0<μ A→A⊆E)
    (hdom : ∀ a,(∑ A,μ A*uniformWeight A a)≤C*p a) :
    ∀ a,(∑ A,μ A*uniformWeight (μ.repair A) a)≤C*conditionOn p E hE a := by
  intro a
  rw [μ.repair_mean (fun A=>uniformWeight A a)]
  have h:=supported_levels_conditioned_domination μ p E hE C hC hsub hdom a
  rw [positiveLaw_mean μ (fun A=>uniformWeight A a)] at h
  exact h
end
end SharpRamseyFive.FiniteEntropy

end OAI
