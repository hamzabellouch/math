import OAI.Probability.MatroidProphet.Main

namespace OAI

/-!
# The layer rule is the source's accepted-prefix greedy rule

The implementation tests the span of all previous eligible labels. The source
algorithm tests the span of the previous accepted labels. Prefix span preservation
makes these tests exactly equal, not merely comparable in final reward.
-/

namespace MatroidProphet
open Set Finset

lemma layerGreedy_closure_prefix {α : Type*} [DecidableEq α]
    (M : Matroid α) (E : Finset α) (base : ℤ → Set α)
    (layer : α → ℤ) (time : α → ℕ) (hE : M.E = Set.univ) (b : ℤ) (k : ℕ) :
    M.closure (base b ∪ layerPrior E layer time b k) =
      M.closure (base b ∪
        {e | e ∈ layerGreedy M E base layer time ∧ layer e = b ∧ time e < k}) := by
  apply Set.Subset.antisymm
  · apply M.closure_subset_closure_of_subset_closure
    rintro e (he | ⟨he, hb, ht⟩)
    · exact M.mem_closure_of_mem' (Or.inl he) (by simp [hE])
    · have hs := layerGreedy_spans_prefix M E base layer time hE e he
      apply M.closure_subset_closure _ hs
      rintro f (hf | ⟨hf, hfb, hft⟩)
      · exact Or.inl (by simpa only [hb] using hf)
      · exact Or.inr ⟨hf, hfb.trans hb, hft.trans_lt ht⟩
  · apply M.closure_subset_closure
    rintro e (he | ⟨he, hb, ht⟩)
    · exact Or.inl he
    · exact Or.inr ⟨layerGreedy_subset M E base layer time he, hb, ht⟩

/-- The actual layer acceptance test may use only its earlier accepted labels. -/
theorem layerGreedy_mem_iff_accepted_prefix {α : Type*} [DecidableEq α]
    (M : Matroid α) (E : Finset α) (base : ℤ → Set α)
    (layer : α → ℤ) (time : α → ℕ) (hE : M.E = Set.univ) (e : α) :
    e ∈ layerGreedy M E base layer time ↔
      e ∈ E ∧ e ∉ M.closure (base (layer e) ∪
        {f | f ∈ layerGreedy M E base layer time ∧
          layer f = layer e ∧ time f < time e}) := by
  classical
  rw [show e ∈ layerGreedy M E base layer time ↔ e ∈ E ∧
    e ∉ M.closure (base (layer e) ∪ layerPrior E layer time (layer e) (time e)) from
      Finset.mem_filter]
  rw [layerGreedy_closure_prefix M E base layer time hE]

/-- Exact conditional-rank form of the source test at an arrival. -/
theorem layerGreedy_mem_iff_rank_one {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (E : Finset α) (base : ℤ → Set α)
    (layer : α → ℤ) (time : α → ℕ) (hE : M.E = Set.univ) (e : α) :
    e ∈ layerGreedy M E base layer time ↔
      e ∈ E ∧ conditionalRank M {e} (base (layer e) ∪
        {f | f ∈ layerGreedy M E base layer time ∧
          layer f = layer e ∧ time f < time e}) = 1 := by
  rw [layerGreedy_mem_iff_accepted_prefix M E base layer time hE]
  constructor
  · rintro ⟨he, hne⟩
    exact ⟨he, Pivots.conditionalRank_singleton_of_notMem_closure M _
      (by simp [hE]) hne⟩
  · rintro ⟨he, hr⟩
    refine ⟨he, ?_⟩
    intro hmem
    have hz := Pivots.conditionalRank_singleton_of_mem_closure M _ hmem
    omega

end MatroidProphet

end OAI
