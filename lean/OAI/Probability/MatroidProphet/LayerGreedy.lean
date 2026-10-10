import OAI.Probability.MatroidProphet.RankAccounting
import Mathlib.Data.Finset.Max

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [DecidableEq α]

noncomputable def layerPrior (E : Finset α) (layer : α → ℤ) (time : α → ℕ)
    (b : ℤ) (k : ℕ) : Set α := {e | e ∈ E ∧ layer e = b ∧ time e < k}

noncomputable def layerGreedy (M : Matroid α) (E : Finset α)
    (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ) : Finset α := by
  classical
  exact E.filter fun e => e ∉ M.closure (base (layer e) ∪ layerPrior E layer time (layer e) (time e))

omit [DecidableEq α] in
lemma layerGreedy_subset (M : Matroid α) (E : Finset α)
    (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ) :
    layerGreedy M E base layer time ⊆ E := by
  classical
  exact filter_subset _ _

omit [DecidableEq α] in
lemma layerPrior_mono (E : Finset α) (layer : α → ℤ) (time : α → ℕ)
    (b : ℤ) {k k' : ℕ} (h : k ≤ k') :
    layerPrior E layer time b k ⊆ layerPrior E layer time b k' := by
  rintro e ⟨he, hb, ht⟩
  exact ⟨he, hb, lt_of_lt_of_le ht h⟩

lemma layerGreedy_spans_prefix (M : Matroid α) (E : Finset α)
    (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ)
    (hE : M.E = Set.univ) (e : α) (he : e ∈ E) :
    e ∈ M.closure (base (layer e) ∪
      {f | f ∈ layerGreedy M E base layer time ∧ layer f = layer e ∧ time f ≤ time e}) := by
  have aux : ∀ k, ∀ e ∈ E, time e = k →
      e ∈ M.closure (base (layer e) ∪
        {f | f ∈ layerGreedy M E base layer time ∧ layer f = layer e ∧ time f ≤ k}) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro e he htime
      by_cases hkeep : e ∈ layerGreedy M E base layer time
      · exact M.mem_closure_of_mem' (Or.inr ⟨hkeep, rfl, htime.le⟩) (by simp [hE])
      have hdep : e ∈ M.closure (base (layer e) ∪ layerPrior E layer time (layer e) (time e)) := by
        simpa only [layerGreedy, mem_filter, he, true_and, not_not] using hkeep
      apply M.closure_subset_closure_of_subset_closure ?_ hdep
      rintro f (hf | ⟨hf, hl, ht⟩)
      · exact M.mem_closure_of_mem' (Or.inl hf) (by simp [hE])
      · have hfk : time f < k := by simpa [htime] using ht
        have hrec := ih (time f) hfk f hf rfl
        apply M.closure_subset_closure ?_ hrec
        rintro g (hg | ⟨hg, hgl, hgt⟩)
        · exact Or.inl (by simpa [hl] using hg)
        · exact Or.inr ⟨hg, hgl.trans hl, hgt.trans hfk.le⟩
  exact aux (time e) e he rfl

theorem layerGreedy_indep (M : Matroid α) (E : Finset α)
    (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ)
    (hE : M.E = Set.univ) (htime : Function.Injective time)
    (hlower : ∀ e ∈ E, ∀ f ∈ E, layer e < layer f → e ∈ base (layer f)) :
    M.Indep (layerGreedy M E base layer time : Set α) := by
  classical
  suffices aux : ∀ A : Finset α, A ⊆ layerGreedy M E base layer time →
      M.Indep (A : Set α) from aux _ Finset.Subset.rfl
  intro A
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    intro hA
    by_cases hne : A.Nonempty
    · obtain ⟨p₀, hp₀, hmaxLayer⟩ := exists_max_image A layer hne
      have htne : (A.filter (fun e => layer e = layer p₀)).Nonempty :=
        ⟨p₀, mem_filter.mpr ⟨hp₀, rfl⟩⟩
      obtain ⟨p, hpt, hmaxTime⟩ := exists_max_image
        (A.filter (fun e => layer e = layer p₀)) time htne
      have hp : p ∈ A := (mem_filter.mp hpt).1
      have hpl : layer p = layer p₀ := (mem_filter.mp hpt).2
      have hpE := layerGreedy_subset M E base layer time (hA hp)
      have hI := ih (A.erase p) (erase_ssubset hp)
        (fun e he => hA (mem_of_mem_erase he))
      have hnot : p ∉ M.closure (A.erase p : Set α) := by
        intro hmem
        have hpnot := (mem_filter.mp (hA hp)).2
        apply hpnot
        apply M.closure_subset_closure ?_ hmem
        intro q hq
        have hqA := mem_of_mem_erase hq
        have hqE := layerGreedy_subset M E base layer time (hA hqA)
        have hqle : layer q ≤ layer p := by simpa [hpl] using hmaxLayer q hqA
        rcases lt_or_eq_of_le hqle with hqlt | hqeq
        · exact Or.inl (hlower q hqE p hpE hqlt)
        · refine Or.inr ⟨hqE, hqeq, ?_⟩
          have hqt : q ∈ A.filter (fun e => layer e = layer p₀) :=
            mem_filter.mpr ⟨hqA, hqeq.trans hpl⟩
          exact lt_of_le_of_ne (hmaxTime q hqt) (fun h => (ne_of_mem_erase hq) (htime h))
      have hins := hI.insert_indep_iff.mpr (Or.inl ⟨by simp [hE], hnot⟩)
      simpa only [← Finset.coe_insert, insert_erase hp] using hins
    · have hzero := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hzero]

lemma layerGreedy_spans (M : Matroid α) (E : Finset α)
    (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ)
    (hE : M.E = Set.univ) (b : ℤ) :
    {e | e ∈ E ∧ layer e = b} ⊆
      M.closure (base b ∪ {e | e ∈ layerGreedy M E base layer time ∧ layer e = b}) := by
  rintro e ⟨he, hb⟩
  have h := layerGreedy_spans_prefix M E base layer time hE e he
  apply M.closure_subset_closure ?_ h
  rintro f (hf | ⟨hf, hfb, _⟩)
  · exact Or.inl (by simpa [hb] using hf)
  · exact Or.inr ⟨hf, hfb.trans hb⟩

end MatroidProphet

end OAI
