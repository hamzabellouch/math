import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! Exact agreement between the source's previous-accepted-label test and the
concrete implementation's previous-eligible-label test. No arrival-order
assumption beyond the explicit arrival times is used in span preservation. -/

namespace MatroidProphet
open Set Finset

variable {α : Type*} [DecidableEq α]

/-- Rejected earlier eligible labels do not change the span of a layer prefix. -/
theorem layerGreedy_closure_prior (M : Matroid α) (E : Finset α)
    (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ)
    (hE : M.E = Set.univ) (b : ℤ) (k : ℕ) :
    M.closure (base b ∪ layerPrior E layer time b k) =
      M.closure (base b ∪
        layerPrior (layerGreedy M E base layer time) layer time b k) := by
  apply Set.Subset.antisymm
  · apply M.closure_subset_closure_of_subset_closure
    rintro e (he | ⟨he, hb, ht⟩)
    · exact M.mem_closure_of_mem' (Or.inl he) (by simp [hE])
    · have hs := layerGreedy_spans_prefix M E base layer time hE e he
      apply M.closure_subset_closure ?_ hs
      rintro f (hf | ⟨hf, hfb, hft⟩)
      · exact Or.inl (by simpa [hb] using hf)
      · exact Or.inr ⟨hf, hfb.trans hb, hft.trans_lt ht⟩
  · apply M.closure_subset_closure
    rintro e (he | ⟨he, hb, ht⟩)
    · exact Or.inl he
    · exact Or.inr ⟨layerGreedy_subset M E base layer time he, hb, ht⟩

/-- The online decision can be implemented using only earlier accepted labels
of the same layer, exactly as in step 3 of the manuscript algorithm. -/
theorem layerGreedy_mem_iff_previous_accepted (M : Matroid α) (E : Finset α)
    (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ)
    (hE : M.E = Set.univ) (e : α) :
    e ∈ layerGreedy M E base layer time ↔
      e ∈ E ∧ e ∉ M.closure (base (layer e) ∪
        layerPrior (layerGreedy M E base layer time) layer time (layer e) (time e)) := by
  classical
  conv_lhs => unfold layerGreedy
  rw [Finset.mem_filter]
  rw [layerGreedy_closure_prior M E base layer time hE]

omit [DecidableEq α] in
/-- On a finite ground set the source's rank-one test is precisely nonmembership
in the closure, including rank-zero and loop cases. -/
theorem conditionalRank_singleton_eq_one_iff [Fintype α] (M : Matroid α)
    (hE : M.E = Set.univ) (P : Set α) (e : α) :
    conditionalRank M {e} P = 1 ↔ e ∉ M.closure P := by
  by_cases he : e ∈ M.closure P
  · rw [Pivots.conditionalRank_singleton_of_mem_closure M P he]
    simp [he]
  · rw [Pivots.conditionalRank_singleton_of_notMem_closure M P (by simp [hE]) he]
    simp [he]

/-- Exact rank form of the source's accept/reject condition. -/
theorem layerGreedy_mem_iff_rank_previous_accepted [Fintype α]
    (M : Matroid α) (E : Finset α) (base : ℤ → Set α)
    (layer : α → ℤ) (time : α → ℕ) (hE : M.E = Set.univ) (e : α) :
    e ∈ layerGreedy M E base layer time ↔
      e ∈ E ∧ conditionalRank M {e} (base (layer e) ∪
        layerPrior (layerGreedy M E base layer time) layer time (layer e) (time e)) = 1 := by
  rw [layerGreedy_mem_iff_previous_accepted M E base layer time hE,
    conditionalRank_singleton_eq_one_iff M hE]

/-- The concrete history-based online decision agrees with the rank test on
previously accepted labels in the current layer. -/
theorem layerKeyDecision_eq_rank_previous_accepted {n : ℕ} {K : Type*}
    (M : Matroid (Fin n)) (hE : M.E = Set.univ) (base : ℤ → Set (Fin n))
    (assign : Fin n → K → Option ℤ) (v : Fin n → K)
    (π : ArrivalOrder n) (k : Fin n) :
    layerKeyDecision M base assign k (keyHistory v π k) = true ↔
      π k ∈ assignedEligible assign v ∧
      conditionalRank M {π k} (base (assignedLayer assign v (π k)) ∪
        layerPrior
          (layerGreedy M (assignedEligible assign v) base (assignedLayer assign v)
            (fun e => (π.symm e).val))
          (assignedLayer assign v) (fun e => (π.symm e).val)
          (assignedLayer assign v (π k)) k.val) = 1 := by
  rw [layerKeyDecision_eq_greedy,
    layerGreedy_mem_iff_rank_previous_accepted M _ _ _ _ hE]
  simp only [Equiv.symm_apply_apply]

end MatroidProphet

end OAI
