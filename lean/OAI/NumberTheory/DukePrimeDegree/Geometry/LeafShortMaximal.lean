import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafCompactMaximal

namespace OAI

/-!
# Short-interval maximal control with a small exceptional set

Inner regularity and the compact-set estimate give uniform relative
maximal control at sufficiently short times. The error is the measure
of the complement of a large compact set.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem short_interval_intrinsic_maximal_bound
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ (M : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ (B E : Set (X n)), MeasurableSet B → MeasurableSet E → ∀ c : ℝ≥0∞,
      (∀ᵐ x ∂μ, x ∈ B → ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧
        c * intrinsicRootLeaf hij μ x (closedBall 0 r) ≤
          intrinsicRootLeaf hij μ x
            ({u | rightAction x (Matrix.SpecialLinearGroup.transvection hij u) ∈ E} ∩
              closedBall 0 r)) →
      c * μ B ≤ (M : ℝ≥0∞) * μ E + c * ε := by
  obtain ⟨K, _, hK, hsmall⟩ := MeasurableSet.univ.exists_isCompact_sdiff_lt
    (μ := μ) (measure_ne_top μ univ) hε
  have hKsmall : μ Kᶜ < ε := by simpa only [← compl_eq_univ_sdiff] using hsmall
  obtain ⟨M, δ, hδ, hbound⟩ := compact_intrinsic_maximal_bound hij K hK
  refine ⟨M, δ, hδ, ?_⟩
  intro B E hB hE c hbad
  have hbadK : ∀ᵐ x ∂μ, x ∈ B ∩ K → ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧
      c * intrinsicRootLeaf hij μ x (closedBall 0 r) ≤
        intrinsicRootLeaf hij μ x
          ({u | rightAction x (Matrix.SpecialLinearGroup.transvection hij u) ∈ E} ∩
            closedBall 0 r) := hbad.mono fun _ hx h => hx h.1
  have hBK := hbound μ hfree (B ∩ K) E (hB.inter hK.measurableSet) hE
    inter_subset_right c hbadK
  calc
    c * μ B ≤ c * (μ (B ∩ K) + μ Kᶜ) := mul_le_mul' le_rfl
      ((measure_mono (show B ⊆ (B ∩ K) ∪ Kᶜ by intro x hx; by_cases h : x ∈ K <;> tauto)).trans
        (measure_union_le _ _))
    _ = c * μ (B ∩ K) + c * μ Kᶜ := mul_add ..
    _ ≤ (M : ℝ≥0∞) * μ E + c * ε :=
      add_le_add hBK (mul_le_mul' le_rfl hKsmall.le)

end DukePrimeDegree

end

end OAI
