import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set MeasureTheory
open scoped ENNReal
namespace YauCounterexamples

theorem probability_bad_jet_le {Ω X V I : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace X] [NormedAddCommGroup V] [Fintype I]
    (μ : Measure Ω) (F : Ω → X → V) (G : Set Ω) (K : Set X) (p : I → X)
    (δ τ L : ℝ) (hL : 0 ≤ L)
    (hcover : ∀ x ∈ K, ∃ i, dist x (p i) ≤ δ)
    (hLip : ∀ outcome ∈ G, ∀ x ∈ K, ∀ i, ‖F outcome x - F outcome (p i)‖ ≤ L * dist x (p i))
    (q : ℝ≥0∞) (hsmall : ∀ i, μ {outcome | ‖F outcome (p i)‖ < τ + L * δ} ≤ q) :
    μ {outcome | ∃ x ∈ K, ‖F outcome x‖ < τ} ≤ μ Gᶜ + Fintype.card I * q := by
  have hsub : {outcome | ∃ x ∈ K, ‖F outcome x‖ < τ} ⊆
      Gᶜ ∪ ⋃ i, {outcome | ‖F outcome (p i)‖ < τ + L * δ} := by
    intro outcome hω
    by_cases hG : outcome ∈ G
    · obtain ⟨x, hx, hFx⟩ := hω
      obtain ⟨i, hi⟩ := hcover x hx
      refine Or.inr (Set.mem_iUnion.mpr ⟨i, ?_⟩)
      have hh := (hLip outcome hG x hx i).trans (mul_le_mul_of_nonneg_left hi hL)
      have ht := norm_sub_norm_le (F outcome (p i)) (F outcome x)
      rw [norm_sub_rev] at ht
      change ‖F outcome (p i)‖ < τ + L * δ
      linarith
    · exact Or.inl hG
  calc
    μ {outcome | ∃ x ∈ K, ‖F outcome x‖ < τ} ≤
        μ (Gᶜ ∪ ⋃ i, {outcome | ‖F outcome (p i)‖ < τ + L * δ}) := measure_mono hsub
    _ ≤ μ Gᶜ + μ (⋃ i, {outcome | ‖F outcome (p i)‖ < τ + L * δ}) := measure_union_le _ _
    _ ≤ μ Gᶜ + ∑ i, μ {outcome | ‖F outcome (p i)‖ < τ + L * δ} :=
      add_le_add le_rfl (measure_iUnion_fintype_le μ _)
    _ ≤ μ Gᶜ + ∑ _i : I, q := add_le_add le_rfl (Finset.sum_le_sum fun i _ => hsmall i)
    _ = μ Gᶜ + Fintype.card I * q := by simp

theorem exists_good_of_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ)
    (hF : Integrable F μ) (G : Set Ω) (hG : MeasurableSet G)
    (C a c : ℝ) (hC : ∀ outcome, F outcome ≤ C) (hc : 0 ≤ c)
    (ha : a ≤ ∫ outcome, F outcome ∂μ) (hbad : c + C * (μ Gᶜ).toReal < a) :
    ∃ outcome ∈ G, c < F outcome := by
  by_contra h
  push Not at h
  let B : Ω → ℝ := fun outcome => c + Gᶜ.indicator (fun _ => C) outcome
  have hB : Integrable B μ := (integrable_const c).add
    ((integrable_const C).indicator hG.compl)
  have hFB : ∀ outcome, F outcome ≤ B outcome := by
    intro outcome
    by_cases hω : outcome ∈ G
    · simpa [B, hω] using h outcome hω
    · simp only [B, Set.indicator_of_mem (show outcome ∈ Gᶜ from hω)]
      linarith [hC outcome]
  have hint : (∫ outcome, B outcome ∂μ) = c + C * (μ Gᶜ).toReal := by
    dsimp only [B]
    rw [integral_add (integrable_const c) ((integrable_const C).indicator hG.compl),
      integral_indicator hG.compl]
    simp [mul_comm, Measure.real]
  exact (not_lt_of_ge (ha.trans ((integral_mono hF hB hFB).trans_eq hint))) hbad

end YauCounterexamples

end

end OAI
