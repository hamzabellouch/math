import OAI.Geometry.HeilbronnTriangle.ShortestIntegralVector

namespace OAI


namespace Problem355.IntegralMinima

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

lemma independent_pair_not_both_mem_line
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (a b c : E) (hab : LinearIndependent ℝ ![a, b]) :
    a ∉ Submodule.span ℝ {c} ∨ b ∉ Submodule.span ℝ {c} := by
  by_contra! h
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp h.1
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h.2
  have hpair := linearIndependent_fin2.mp hab
  have htne : t ≠ 0 := by
    intro htzero
    apply hpair.1
    change b = 0
    simpa only [htzero, zero_smul] using ht.symm
  apply hpair.2 (s / t)
  change (s / t) • b = a
  rw [← ht, smul_smul, div_mul_cancel₀ s htne, hs]

theorem exists_shortest_pair (S : Set (ι → ℤ))
    (a b : ι → ℤ) (ha : a ∈ S) (hb : b ∈ S)
    (hab : LinearIndependent ℝ ![toEuclidean a, toEuclidean b]) :
    ∃ v w : ι → ℤ,
      v ∈ S ∧ w ∈ S ∧ toEuclidean v ≠ 0 ∧
      toEuclidean w ∉ Submodule.span ℝ {toEuclidean v} ∧
      1 ≤ ‖toEuclidean v‖ ∧ ‖toEuclidean v‖ ≤ ‖toEuclidean w‖ ∧
      (∀ x ∈ S, toEuclidean x ≠ 0 → ‖toEuclidean v‖ ≤ ‖toEuclidean x‖) ∧
      (∀ x ∈ S, toEuclidean x ∉ Submodule.span ℝ {toEuclidean v} →
        ‖toEuclidean w‖ ≤ ‖toEuclidean x‖) ∧
      ‖toEuclidean v‖ ≤ ‖toEuclidean a‖ ∧
      ‖toEuclidean w‖ ≤ max ‖toEuclidean a‖ ‖toEuclidean b‖ := by
  have hane : toEuclidean a ≠ 0 := by
    simpa only [Matrix.cons_val_zero] using hab.ne_zero (0 : Fin 2)
  obtain ⟨v, hv, hvbot, hvone, hvmin⟩ := exists_shortest_outside S ⊥
    ⟨a, ha, by simpa only [Submodule.mem_bot] using hane⟩
  have hvne : toEuclidean v ≠ 0 := by
    simpa only [Submodule.mem_bot] using hvbot
  have hex : ∃ w ∈ S, toEuclidean w ∉ Submodule.span ℝ {toEuclidean v} := by
    rcases independent_pair_not_both_mem_line (toEuclidean a) (toEuclidean b)
      (toEuclidean v) hab with h | h
    · exact ⟨a, ha, h⟩
    · exact ⟨b, hb, h⟩
  obtain ⟨w, hw, hwline, _, hwmin⟩ := exists_shortest_outside S
    (Submodule.span ℝ {toEuclidean v}) hex
  have hwne : toEuclidean w ≠ 0 := by
    intro hzero
    exact hwline (hzero ▸ Submodule.zero_mem _)
  have hvmin' : ∀ x ∈ S, toEuclidean x ≠ 0 →
      ‖toEuclidean v‖ ≤ ‖toEuclidean x‖ := by
    intro x hx hxne
    exact hvmin x hx (by simpa only [Submodule.mem_bot] using hxne)
  refine ⟨v, w, hv, hw, hvne, hwline, hvone, hvmin' w hw hwne,
    hvmin', hwmin, hvmin' a ha hane, ?_⟩
  rcases independent_pair_not_both_mem_line (toEuclidean a) (toEuclidean b)
    (toEuclidean v) hab with h | h
  · exact (hwmin a ha h).trans (le_max_left _ _)
  · exact (hwmin b hb h).trans (le_max_right _ _)

end Problem355.IntegralMinima

end OAI
