import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportTemplates

namespace OAI

/-! # Monotonicity and strictness of the weighted template support -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open Set
open scoped BigOperators

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : PolycyclicRecognition.SupportDatum W I B)

omit [Nonempty B] in
theorem weightSupport_eq_of_bound_and_attained {E : Set W} (hc : IsCompact E)
    (i : I) (r : ℝ) (hbound : ∀ x ∈ E, D.weight i x ≤ r)
    (hattained : ∃ x ∈ E, D.weight i x = r) : D.weightSupport E i = r := by
  obtain ⟨x, hx, heq⟩ := hattained
  apply le_antisymm
  · obtain ⟨y, hy, hsup⟩ := D.exists_weightSupport_point hc ⟨x, hx⟩ i
    rw [hsup]
    exact hbound y hy
  · rw [← heq]
    exact D.weight_le_weightSupport hc hx i

omit [Nonempty B] in
theorem weightSupport_mono {E F : Set W} (hE : IsCompact E) (hn : E.Nonempty)
    (hF : IsCompact F) (hEF : E ⊆ F) (i : I) :
    D.weightSupport E i ≤ D.weightSupport F i := by
  obtain ⟨x, hx, heq⟩ := D.exists_weightSupport_point hE hn i
  rw [heq]
  exact D.weight_le_weightSupport hF (hEF hx) i

omit [FiniteDimensional ℝ W] in
/-- Every word basis contains every generator with positive multiplicity,
so decreasing one support strictly decreases the entire finite maximum. -/
theorem templateSupport_lt_of_weightSupport {E F : Set W}
    (hle : ∀ i, D.weightSupport E i ≤ D.weightSupport F i)
    (hlt : ∃ i, D.weightSupport E i < D.weightSupport F i) :
    D.templateSupport E < D.templateSupport F := by
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (D.basisTemplateSupport E)
  change Finset.univ.sup' _ _ < _
  rw [hb]
  apply lt_of_lt_of_le _ (D.basisTemplateSupport_le F b)
  unfold basisTemplateSupport
  apply Finset.sum_lt_sum
  · intro i _
    exact mul_le_mul_of_nonneg_left (hle i) (Nat.cast_nonneg _)
  · obtain ⟨i, hi⟩ := hlt
    exact ⟨i, Finset.mem_univ i,
      mul_lt_mul_of_pos_left hi (Nat.cast_pos.mpr (D.positive b i))⟩

end PolycyclicRecognition.SupportDatum

end

end OAI
