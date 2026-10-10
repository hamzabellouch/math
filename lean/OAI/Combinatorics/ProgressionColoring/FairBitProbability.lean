import OAI.Combinatorics.ProgressionColoring.FairBitTail
import OAI.Combinatorics.ProgressionColoring.FiniteProbability

namespace OAI

universe uLabel

namespace QuantitativeVanDerWaerden

variable {Label : Type uLabel} [Fintype Label] [DecidableEq Label]

/-- A support fails balancing when one bit occurs fewer than a quarter of its
distinct labels. -/
noncomputable def fairBalancingBad (S : Finset Label) : Finset (Label → Bool) := by
  classical
  exact Finset.univ.filter fun ω =>
    ∃ b : Bool, 4 * (S.filter fun i => ω i = b).card < S.card

@[simp] theorem mem_fairBalancingBad (S : Finset Label) (ω : Label → Bool) :
    ω ∈ fairBalancingBad S ↔
      ∃ b : Bool, 4 * (S.filter fun i => ω i = b).card < S.card := by
  classical
  simp [fairBalancingBad]

/-- Avoiding the event says that both bits occupy at least a quarter. -/
theorem not_mem_fairBalancingBad_iff (S : Finset Label) (ω : Label → Bool) :
    ω ∉ fairBalancingBad S ↔
      ∀ b : Bool, S.card ≤ 4 * (S.filter fun i => ω i = b).card := by
  simp only [mem_fairBalancingBad, not_exists, not_lt]

/-- Agreement on the tested labels preserves membership in the bad event. -/
theorem fairBalancingBad_depends (S : Finset Label) (ω η : Label → Bool)
    (h : ∀ i ∈ S, ω i = η i) :
    ω ∈ fairBalancingBad S ↔ η ∈ fairBalancingBad S := by
  classical
  have hf (b : Bool) :
      S.filter (fun i => ω i = b) = S.filter (fun i => η i = b) := by
    apply Finset.filter_congr
    intro i hi
    rw [h i hi]
  simp only [mem_fairBalancingBad, hf]

theorem bernoulli_half_eq_fairWeight {Label : Type uLabel} [Fintype Label] [DecidableEq Label]
    (ω : Label → Bool) :
    FiniteProbability.bernoulliWeight (1 / 2) ω = FairBitTail.weight ω := by
  unfold FiniteProbability.bernoulliWeight FairBitTail.weight
  apply Finset.prod_congr rfl
  intro i _
  cases ω i <;> norm_num [FiniteProbability.bitWeight]

/-- The actual bad-event probability under independent fair Boolean labels. -/
theorem fair_balancing_tail (S : Finset Label) :
    FiniteProbability.prob (FiniteProbability.bernoulliWeight (1 / 2))
      (fairBalancingBad S) ≤ 2 * Real.exp (-(S.card : ℝ) / 8) := by
  classical
  unfold FiniteProbability.prob fairBalancingBad
  rw [Finset.sum_filter]
  simp_rw [bernoulli_half_eq_fairWeight]
  exact FairBitTail.balancing_tail S

end QuantitativeVanDerWaerden

end OAI
