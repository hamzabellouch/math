import OAI.Combinatorics.KMedianRecovery.Recovery.State2

namespace OAI

/-! Appending dummy leaves decreases reference distances and preserves retained assignments. -/

namespace MetricKMedianRecovery.Sampling
namespace State
variable {V : Type*}

def extend (s : State V) (L : List (V × ℝ)) : State V :=
  ⟨s.deleted, s.leaves ++ L⟩
end State

variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

omit [PseudoMetricSpace V] in
lemma tags_extend_mono (S : Finset V) (s : State V) (L : List (V × ℝ)) :
    tags S s ⊆ tags S (s.extend L) := by
  unfold tags
  apply Finset.union_subset_union_right
  exact Finset.image_subset_image (Finset.range_mono (by simp [State.extend]))

lemma tagDistance_extend_old (S : Finset V) (Δ : ℝ) (s : State V) (L : List (V × ℝ))
    (x : V) {t : Tag V} (ht : t ∈ tags S s) :
    tagDistance Δ (s.extend L) x t = tagDistance Δ s x t := by
  cases he : ofLex t with
  | inl v => simp only [tagDistance, he]
  | inr j =>
    have htag : t = leafTag j := by exact congrArg toLex he
    have hj := (leaf_mem_tags S s j).mp (htag ▸ ht)
    cases j with
    | zero => simp only [tagDistance, he]
    | succ j =>
      have hj' : j < s.leaves.length := by omega
      simp only [tagDistance, he, State.extend, List.getElem?_append, hj', ↓reduceIte]

lemma reference_extend_le (S : Finset V) (Δ : ℝ) (s : State V)
    (L : List (V × ℝ)) (x : V) :
    reference S Δ (s.extend L) x ≤ reference S Δ s x := by
  have hh := reference_le S Δ (s.extend L) x
    (tags_extend_mono S s L (chosen_mem S Δ s x))
  exact hh.trans_eq (tagDistance_extend_old S Δ s L x (chosen_mem S Δ s x))

lemma chosen_extend_consistent (S : Finset V) (Δ : ℝ) (s : State V)
    (L : List (V × ℝ)) (x : V) (hold : chosen S Δ (s.extend L) x ∈ tags S s) :
    chosen S Δ (s.extend L) x = chosen S Δ s x := by
  have h₁ := chosen_key_le S Δ s x hold
  have h₂ := chosen_key_le S Δ (s.extend L) x (tags_extend_mono S s L (chosen_mem S Δ s x))
  rw [tagDistance_extend_old S Δ s L x hold,
    tagDistance_extend_old S Δ s L x (chosen_mem S Δ s x)] at h₂
  exact congrArg (fun z : ℝ ×ₗ Tag V => (ofLex z).2) (le_antisymm h₂ h₁)

noncomputable def assignedOriginals (D S R : Finset V) (Δ : ℝ) (s : State V) : Finset V :=
  D.filter (fun p => ∃ r ∈ R, chosen S Δ s p = realTag r)

lemma assignedOriginals_extend_subset (D S R : Finset V) (Δ : ℝ) (s : State V)
    (L : List (V × ℝ)) :
    assignedOriginals D S R Δ (s.extend L) ⊆ assignedOriginals D S R Δ s := by
  intro p hp
  obtain ⟨hpD, r, hr, he⟩ := Finset.mem_filter.mp hp
  have hmem : realTag r ∈ tags S (s.extend L) := he ▸ chosen_mem S Δ (s.extend L) p
  have hold : realTag r ∈ tags S s := by
    rw [real_mem_tags] at hmem ⊢
    exact hmem
  have hc := chosen_extend_consistent S Δ s L p (he.symm ▸ hold)
  exact Finset.mem_filter.mpr ⟨hpD, r, hr, hc.symm.trans he⟩

lemma internalCost_extend_le (D S R : Finset V) (Δ : ℝ) (s : State V)
    (L : List (V × ℝ)) (hΔ : 0 ≤ Δ) (hr : ∀ z ∈ s.leaves, 0 ≤ z.2) :
    (∑ p ∈ assignedOriginals D S R Δ (s.extend L), reference S Δ (s.extend L) p) ≤
      ∑ p ∈ assignedOriginals D S R Δ s, reference S Δ s p := by
  apply (Finset.sum_le_sum (fun p _ => reference_extend_le S Δ s L p)).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg (assignedOriginals_extend_subset D S R Δ s L)
    (fun p _ _ => reference_nonneg S Δ s p hΔ hr)
end MetricKMedianRecovery.Sampling

end OAI
