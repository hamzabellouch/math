import Mathlib

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace PlanarEndpoint.TransverseInformation

lemma joint_laws_tight {μs : ℕ → ProbabilityMeasure (ℕ → ℝ)}
    (htail : ∀ i : ℕ, ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ,
      ∀ n, (μs n : Measure (ℕ → ℝ)) {x | R < |x i|} ≤ ε) :
    IsTightMeasureSet (Set.range (fun n => (μs n : Measure (ℕ → ℝ)))) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
  choose R hR using fun i => htail i (δ i) (hδpos i)
  let K : Set (ℕ → ℝ) := {x | ∀ i, x i ∈ Set.Icc (-(R i)) (R i)}
  have hK : IsCompact K := isCompact_pi_infinite (fun _ => isCompact_Icc)
  refine ⟨K, hK, ?_⟩
  rintro μ ⟨n, rfl⟩
  have hsubset : Kᶜ ⊆ ⋃ i, {x : ℕ → ℝ | R i < |x i|} := by
    intro x hx
    change ¬ (∀ i, -(R i) ≤ x i ∧ x i ≤ R i) at hx
    push Not at hx
    obtain ⟨i, hi⟩ := hx
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    change R i < |x i|
    rw [lt_abs]
    by_cases hlo : -(R i) ≤ x i
    · exact Or.inl (hi hlo)
    · exact Or.inr (by linarith)
  calc
    (μs n : Measure (ℕ → ℝ)) Kᶜ ≤
        (μs n : Measure (ℕ → ℝ)) (⋃ i, {x | R i < |x i|}) := measure_mono hsubset
    _ ≤ ∑' i, (μs n : Measure (ℕ → ℝ)) {x | R i < |x i|} := measure_iUnion_le _
    _ ≤ ∑' i, δ i := ENNReal.tsum_le_tsum (fun i => hR i n)
    _ ≤ ε := hδsum.le

lemma exists_joint_weak_limit {μs : ℕ → ProbabilityMeasure (ℕ → ℝ)}
    (htail : ∀ i : ℕ, ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ,
      ∀ n, (μs n : Measure (ℕ → ℝ)) {x | R < |x i|} ≤ ε) :
    ∃ μ : ProbabilityMeasure (ℕ → ℝ), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) := by
  have ht : IsTightMeasureSet
      {((μ : ProbabilityMeasure (ℕ → ℝ)) : Measure (ℕ → ℝ)) | μ ∈ Set.range μs} := by
    convert joint_laws_tight htail using 1
    ext m
    simp only [mem_ofPred_eq, mem_range]
    constructor
    · rintro ⟨μ, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨μs n, ⟨n, rfl⟩, rfl⟩
  have hc := isCompact_closure_of_isTightMeasureSet ht
  obtain ⟨μ, _, φ, hφ, hlim⟩ := hc.isSeqCompact.subseq_of_frequently_in
    (Filter.Eventually.frequently (Filter.Eventually.of_forall
      (fun n => subset_closure (Set.mem_range_self n))))
  exact ⟨μ, φ, hφ, hlim⟩

end PlanarEndpoint.TransverseInformation
end

end OAI
