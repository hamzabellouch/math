import OAI.NumberTheory.Jacobsthal.Estimates.SourceSamplePopulation

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseSampling
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem many_large_weights {α : Type*} (A : Finset α) (f : α → ℝ) (beta : ℝ)
    (hb : 0 ≤ beta) (hf : ∀ a ∈ A,f a ≤ 1) (hmean : beta*(A.card : ℝ) ≤ ∑ a ∈ A,f a) :
    (beta/2)*(A.card : ℝ) ≤ ((A.filter (fun a => beta/2 ≤ f a)).card : ℝ) := by
  have hup : (∑ a ∈ A,f a) ≤
      ((A.filter (fun a => beta/2 ≤ f a)).card : ℝ)+(A.card : ℝ)*(beta/2) := by
    calc
      _ ≤ ∑ a ∈ A,((if beta/2 ≤ f a then (1 : ℝ) else 0)+beta/2) := by
        apply Finset.sum_le_sum
        intro a ha
        by_cases hh : beta/2 ≤ f a
        · rw [ite_eq_left hh]
          linarith [hf a ha]
        · rw [ite_eq_right hh,zero_add]
          exact (lt_of_not_ge hh).le
      _ = _ := by
        rw [Finset.sum_add_distrib,Finset.sum_boole]
        simp
  linarith

noncomputable def witnessPairs {α β : Type*} (A : Finset α) (U : Finset β) (witness : α → β → Prop) :
    Finset (α × β) :=
  (A.product U).filter (fun v => witness v.1 v.2)

theorem witnessPairs_card {α β : Type*} (A : Finset α) (U : Finset β) (witness : α → β → Prop) :
    (witnessPairs A U witness).card = ∑ a ∈ A,(U.filter (witness a)).card := by
  simp only [witnessPairs,Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_product A U (fun v : α × β => if witness v.1 v.2 then (1 : ℕ) else 0)

end ErdosInverseSampling

end

section

namespace ErdosInverseSampling
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def selectedPairs {α β : Type*} (A : Finset α) (U : Finset β)
    (witness : α → β → Prop) (h : ℕ) (e : Sample U h) : Finset α :=
  A.filter (fun a => ∀ i,witness a (e i).val)

noncomputable def selectedFraction {α β : Type*} (A : Finset α) (U : Finset β)
    (witness : α → β → Prop) (h : ℕ) (e : Sample U h) : ℝ :=
  ((selectedPairs A U witness h e).card : ℝ)/(A.card : ℝ)

theorem goodSamples_filter {β : Type*} (U : Finset β) (good : β → Prop) (h : ℕ) :
    goodSamples U (U.filter good) h = Finset.univ.filter (fun e : Sample U h => ∀ i,good (e i).val) := by
  ext e
  simp only [goodSamples,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun he i => (he i).2,fun he i => ⟨(e i).property,he i⟩⟩

theorem sample_incidence_average_eq {α β : Type*} (A : Finset α) (U : Finset β)
    (witness : α → β → Prop) (h : ℕ) :
    sampleAverage U h (selectedFraction A U witness h) =
      (∑ a ∈ A,sampleFrequency U (U.filter (witness a)) h)/(A.card : ℝ) := by
  have hh := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun e : Sample U h => fun a : α => ∀ i,witness a (e i).val) (s := Finset.univ) (t := A)
  have hc : (∑ e : Sample U h,((selectedPairs A U witness h e).card : ℝ)) =
      ∑ a ∈ A,((goodSamples U (U.filter (witness a)) h).card : ℝ) := by
    have hn : (∑ e : Sample U h,(selectedPairs A U witness h e).card) =
        ∑ a ∈ A,(goodSamples U (U.filter (witness a)) h).card := by
      simpa only [selectedPairs,Finset.bipartiteAbove,Finset.bipartiteBelow,goodSamples_filter] using hh
    exact_mod_cast hn
  unfold sampleAverage selectedFraction sampleFrequency
  simp_rw [← Finset.sum_div]
  rw [hc]
  ring

theorem sample_incidence_average_lower {α β : Type*} (A : Finset α) (U : Finset β)
    (witness : α → β → Prop) (h : ℕ) (beta : ℝ) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hA : 0 < A.card) (hU : 0 < U.card)
    (hdense : beta*(A.card : ℝ)*(U.card : ℝ) ≤ ((witnessPairs A U witness).card : ℝ))
    (hsize : 4*(h : ℝ)/beta ≤ (U.card : ℝ)) :
    (beta/2)*(beta/4)^h ≤ sampleAverage U h (selectedFraction A U witness h) := by
  have hAR : (0 : ℝ) < A.card := by exact_mod_cast hA
  have hUR : (0 : ℝ) < U.card := by exact_mod_cast hU
  let f : α → ℝ := fun a => ((U.filter (witness a)).card : ℝ)/(U.card : ℝ)
  let G := A.filter (fun a => beta/2 ≤ f a)
  have hf (a : α) (_ha : a ∈ A) : f a ≤ 1 := by
    apply (div_le_iff₀ hUR).mpr
    simpa only [one_mul] using (Nat.cast_le.mpr (Finset.card_filter_le U (witness a)) :
      ((U.filter (witness a)).card : ℝ) ≤ U.card)
  have hmean : beta*(A.card : ℝ) ≤ ∑ a ∈ A,f a := by
    change beta*(A.card : ℝ) ≤ ∑ a ∈ A,((U.filter (witness a)).card : ℝ)/(U.card : ℝ)
    rw [← Finset.sum_div]
    apply (le_div_iff₀ hUR).mpr
    have he : ((witnessPairs A U witness).card : ℝ) = ∑ a ∈ A,((U.filter (witness a)).card : ℝ) := by
      exact_mod_cast witnessPairs_card A U witness
    rwa [← he]
  have hG : (beta/2)*(A.card : ℝ) ≤ (G.card : ℝ) := many_large_weights A f beta hb.le hf hmean
  have hfreq (a : α) (ha : a ∈ G) : (beta/4)^h ≤ sampleFrequency U (U.filter (witness a)) h := by
    have hh := (Finset.mem_filter.mp ha).2
    have hgood : (beta/2)*(U.card : ℝ) ≤ ((U.filter (witness a)).card : ℝ) := (le_div_iff₀ hUR).mp hh
    exact sampleFrequency_lower U (U.filter (witness a)) (Finset.filter_subset _ _) h beta hb hb1 hgood hsize
  have hnonneg (a : α) : 0 ≤ sampleFrequency U (U.filter (witness a)) h := by
    unfold sampleFrequency
    positivity
  rw [sample_incidence_average_eq]
  apply (le_div_iff₀ hAR).mpr
  calc
    _ ≤ (G.card : ℝ)*(beta/4)^h := by
      have hh := mul_le_mul_of_nonneg_right hG (show 0 ≤ (beta/4)^h by positivity)
      nlinarith only [hh]
    _ = ∑ _a ∈ G,(beta/4)^h := by simp
    _ ≤ ∑ a ∈ G,sampleFrequency U (U.filter (witness a)) h := Finset.sum_le_sum hfreq
    _ ≤ ∑ a ∈ A,sampleFrequency U (U.filter (witness a)) h :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun a _ _ => hnonneg a)

end ErdosInverseSampling

end

end Erdos970

end OAI
