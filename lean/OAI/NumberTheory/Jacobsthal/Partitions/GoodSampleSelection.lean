import OAI.NumberTheory.Jacobsthal.Paths.SampleWitnessAverage

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseSampling
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem exists_reward_cost_sample {Ω : Type*} (S : Finset Ω) (hS : S.Nonempty)
    (reward cost : Ω → ℝ) (gamma tau : ℝ) (hg : 0 < gamma) (ht : 0 < tau)
    (hr : ∀ s ∈ S,reward s ≤ 1) (hc : ∀ s ∈ S,0 ≤ cost s)
    (hreward : gamma*(S.card : ℝ) ≤ ∑ s ∈ S,reward s)
    (hcost : (∑ s ∈ S,cost s) ≤ (gamma*tau/4)*(S.card : ℝ)) :
    ∃ s ∈ S,gamma/2 ≤ reward s ∧ cost s ≤ tau := by
  by_contra h
  push Not at h
  have hpoint (s : Ω) (hs : s ∈ S) : reward s ≤ gamma/2+cost s/tau := by
    by_cases hh : gamma/2 ≤ reward s
    · have hct : tau < cost s := h s hs hh
      have hone : (1 : ℝ) < cost s/tau := (lt_div_iff₀ ht).mpr (by simpa using hct)
      linarith [hr s hs]
    · have hcn : 0 ≤ cost s/tau := div_nonneg (hc s hs) ht.le
      linarith
  have hupper : (∑ s ∈ S,reward s) ≤ (S.card : ℝ)*(gamma/2)+(∑ s ∈ S,cost s)/tau := by
    calc
      _ ≤ ∑ s ∈ S,(gamma/2+cost s/tau) := Finset.sum_le_sum hpoint
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const,nsmul_eq_mul,← Finset.sum_div]
  have hsmall : (∑ s ∈ S,cost s)/tau ≤ (gamma/4)*(S.card : ℝ) := by
    apply (div_le_iff₀ ht).mpr
    nlinarith only [hcost]
  have hN : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hpos : 0 < gamma*(S.card : ℝ) := mul_pos hg hN
  nlinarith only [hreward,hupper,hsmall,hpos]

theorem selectedFraction_le_one {α β : Type*} (A : Finset α) (U : Finset β)
    (witness : α → β → Prop) (h : ℕ) (e : Sample U h) (hA : 0 < A.card) :
    selectedFraction A U witness h e ≤ 1 := by
  have hAR : (0 : ℝ) < A.card := by exact_mod_cast hA
  apply (div_le_iff₀ hAR).mpr
  have hh : (selectedPairs A U witness h e).card ≤ A.card := Finset.card_filter_le A _
  simpa only [one_mul] using (Nat.cast_le.mpr hh : ((selectedPairs A U witness h e).card : ℝ) ≤ A.card)

theorem exists_good_distinct_sample {α β : Type*} (A : Finset α) (U : Finset β)
    (witness : α → β → Prop) (h : ℕ) (beta tau : ℝ) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (ht : 0 < tau) (hA : 0 < A.card) (hU : 0 < U.card)
    (hdense : beta*(A.card : ℝ)*(U.card : ℝ) ≤ ((witnessPairs A U witness).card : ℝ))
    (hsize : 4*(h : ℝ)/beta ≤ (U.card : ℝ)) (cost : Sample U h → ℝ)
    (hc : ∀ e,0 ≤ cost e)
    (hcost : sampleAverage U h cost ≤ (((beta/2)*(beta/4)^h)*tau/4)) :
    ∃ e : Sample U h,((beta/2)*(beta/4)^h)/2 ≤ selectedFraction A U witness h e ∧ cost e ≤ tau := by
  let gamma := (beta/2)*(beta/4)^h
  have hg : 0 < gamma := by dsimp [gamma];positivity
  have hlen := sample_length_le U.card h beta hb hb1 hsize
  have hn : 0 < Fintype.card (Sample U h) := by rw [sample_card];exact Nat.descFactorial_pos.mpr hlen
  have hnR : (0 : ℝ) < Fintype.card (Sample U h) := by exact_mod_cast hn
  have hreward := sample_incidence_average_lower A U witness h beta hb hb1 hA hU hdense hsize
  have hreward' : gamma*(Fintype.card (Sample U h) : ℝ) ≤
      ∑ e : Sample U h,selectedFraction A U witness h e := (le_div_iff₀ hnR).mp hreward
  have hcost' : (∑ e : Sample U h,cost e) ≤ (gamma*tau/4)*(Fintype.card (Sample U h) : ℝ) :=
    (div_le_iff₀ hnR).mp hcost
  obtain ⟨e,_he,her,hec⟩ := exists_reward_cost_sample (Finset.univ : Finset (Sample U h))
    (Finset.card_pos.mp (by simpa only [Finset.card_univ] using hn))
    (selectedFraction A U witness h) cost gamma tau hg ht
    (fun e _ => selectedFraction_le_one A U witness h e hA) (fun e _ => hc e)
    (by simpa only [Finset.card_univ] using hreward') (by simpa only [Finset.card_univ] using hcost')
  exact ⟨e,her,hec⟩

end ErdosInverseSampling

end

end Erdos970

end OAI
