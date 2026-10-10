import Mathlib

namespace OAI

namespace Invariant233

open Set MeasureTheory
open scoped ENNReal

theorem exists_outside_bad_with_finite_tests
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset ι) (F : ι → Ω → ℝ≥0∞) (ε : ι → ℝ≥0∞) (bad : Set Ω)
    (hF : ∀ i ∈ s, AEMeasurable (F i) μ)
    (hε0 : ∀ i ∈ s, ε i ≠ 0) (hεtop : ∀ i ∈ s, ε i ≠ ∞)
    (hbudget : μ bad + ∑ i ∈ s, (∫⁻ ω, F i ω ∂μ) / ε i < 1) :
    ∃ ω, ω ∉ bad ∧ ∀ i ∈ s, F i ω < ε i := by
  classical
  let E := bad ∪ ⋃ i ∈ s, {ω | ε i ≤ F i ω}
  have hmeasure : μ E < 1 := by
    calc
      μ E ≤ μ bad + μ (⋃ i ∈ s, {ω | ε i ≤ F i ω}) := measure_union_le _ _
      _ ≤ μ bad + ∑ i ∈ s, μ {ω | ε i ≤ F i ω} :=
        add_le_add_right (measure_biUnion_finset_le s _) _
      _ ≤ μ bad + ∑ i ∈ s, (∫⁻ ω, F i ω ∂μ) / ε i := by
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro i hi
        exact meas_ge_le_lintegral_div (hF i hi) (hε0 i hi) (hεtop i hi)
      _ < 1 := hbudget
  have hE : E ≠ univ := by
    intro heq
    rw [heq, measure_univ] at hmeasure
    exact lt_irrefl _ hmeasure
  obtain ⟨ω, hω⟩ := Set.nonempty_compl.mpr hE
  refine ⟨ω, ?_, ?_⟩
  · intro hbad
    exact hω (Or.inl hbad)
  · intro i hi
    apply lt_of_not_ge
    intro htest
    exact hω (Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, htest⟩⟩))

theorem exists_outside_bad_with_finite_tests_and_ae
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset ι) (F : ι → Ω → ℝ≥0∞) (ε : ι → ℝ≥0∞) (bad : Set Ω)
    (hF : ∀ i ∈ s, AEMeasurable (F i) μ)
    (hε0 : ∀ i ∈ s, ε i ≠ 0) (hεtop : ∀ i ∈ s, ε i ≠ ∞)
    (hbudget : μ bad + ∑ i ∈ s, (∫⁻ ω, F i ω ∂μ) / ε i < 1)
    (P : Ω → Prop) (hP : ∀ᵐ ω ∂μ, P ω) :
    ∃ ω, P ω ∧ ω ∉ bad ∧ ∀ i ∈ s, F i ω < ε i := by
  have hnull : μ {ω | ¬ P ω} = 0 := ae_iff.mp hP
  have hbudget' : μ (bad ∪ {ω | ¬ P ω}) +
      ∑ i ∈ s, (∫⁻ ω, F i ω ∂μ) / ε i < 1 := by
    calc
      _ ≤ (μ bad + μ {ω | ¬ P ω}) +
          ∑ i ∈ s, (∫⁻ ω, F i ω ∂μ) / ε i :=
        add_le_add_left (measure_union_le _ _) _
      _ = μ bad + ∑ i ∈ s, (∫⁻ ω, F i ω ∂μ) / ε i := by rw [hnull, add_zero]
      _ < 1 := hbudget
  obtain ⟨ω, hω, htests⟩ := exists_outside_bad_with_finite_tests μ s F ε
    (bad ∪ {ω | ¬ P ω}) hF hε0 hεtop hbudget'
  refine ⟨ω, ?_, ?_, htests⟩
  · by_contra hnot
    exact hω (Or.inr hnot)
  · intro hb
    exact hω (Or.inl hb)

theorem exists_finite_tests_of_uniform_expectation_bound
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset ι) (F : ι → Ω → ℝ≥0∞) (bad : Set Ω)
    {ε δ β : ℝ≥0∞} (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞)
    (hF : ∀ i ∈ s, AEMeasurable (F i) μ)
    (hδ : ∀ i ∈ s, (∫⁻ ω, F i ω ∂μ) ≤ δ)
    (hbad : μ bad ≤ β) (hbudget : β + (s.card : ℝ≥0∞) * (δ / ε) < 1)
    (P : Ω → Prop) (hP : ∀ᵐ ω ∂μ, P ω) :
    ∃ ω, P ω ∧ ω ∉ bad ∧ ∀ i ∈ s, F i ω < ε := by
  apply exists_outside_bad_with_finite_tests_and_ae μ s F (fun _ => ε) bad hF
    (fun _ _ => hε0) (fun _ _ => hεtop) _ P hP
  calc
    μ bad + ∑ i ∈ s, (∫⁻ ω, F i ω ∂μ) / ε ≤ β + ∑ _i ∈ s, δ / ε := by
      apply add_le_add hbad
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      exact hδ i hi
    _ = β + (s.card : ℝ≥0∞) * (δ / ε) := by simp [nsmul_eq_mul]
    _ < 1 := hbudget

end Invariant233

end OAI
