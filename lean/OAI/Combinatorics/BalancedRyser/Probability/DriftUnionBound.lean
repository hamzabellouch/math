import OAI.Combinatorics.BalancedRyser.Probability.BoundedDrift

namespace OAI

open MeasureTheory Real Filter
open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced

section
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}

lemma measureReal_le_of_ae_imp {A B : Set Ω}
    (h : ∀ᵐ ω ∂μ, ω ∈ A → ω ∈ B) : μ.real A ≤ μ.real B := by
  exact ENNReal.toReal_mono (measure_ne_top μ B) (measure_mono_ae h)

theorem upper_tail_of_accumulated_drift_bound
    (X : ℕ → Ω → ℝ) (T : ℕ) (L : ℝ) (hT : 1 ≤ T) (hL : 0 < L)
    (hX : ∀ j ≤ T, StronglyMeasurable[ℱ j] (X j))
    (hbound : ∀ j < T, ∀ᵐ ω ∂μ, |X (j + 1) ω - X j ω| ≤ L)
    (u : ℝ) (hu : 0 < u) (t : ℕ) (ht : t ≤ T) (D : ℝ)
    (hD : ∀ᵐ ω ∂μ, (∑ j ∈ Finset.range t,
      μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω) ≤ D) :
    μ.real {ω | D + u ≤ X t ω - X 0 ω} ≤
      2 * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
  apply le_trans (measureReal_le_of_ae_imp ?_)
    (boundedDriftConcentration_proof μ ℱ X T L hT hL hX hbound u hu t ht)
  filter_upwards [hD] with ω hd hω
  exact (by linarith : u ≤ X t ω - X 0 ω - ∑ j ∈ Finset.range t,
    μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω).trans (le_abs_self _)

theorem lower_tail_of_accumulated_drift_bound
    (X : ℕ → Ω → ℝ) (T : ℕ) (L : ℝ) (hT : 1 ≤ T) (hL : 0 < L)
    (hX : ∀ j ≤ T, StronglyMeasurable[ℱ j] (X j))
    (hbound : ∀ j < T, ∀ᵐ ω ∂μ, |X (j + 1) ω - X j ω| ≤ L)
    (u : ℝ) (hu : 0 < u) (t : ℕ) (ht : t ≤ T) (D : ℝ)
    (hD : ∀ᵐ ω ∂μ, D ≤ ∑ j ∈ Finset.range t,
      μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω) :
    μ.real {ω | X t ω - X 0 ω ≤ D - u} ≤
      2 * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
  apply le_trans (measureReal_le_of_ae_imp ?_)
    (boundedDriftConcentration_proof μ ℱ X T L hT hL hX hbound u hu t ht)
  filter_upwards [hD] with ω hd hω
  have hn : u ≤ -(X t ω - X 0 ω - ∑ j ∈ Finset.range t,
    μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω) := by linarith
  exact hn.trans (neg_le_abs _)

theorem abs_tail_of_accumulated_drift_bound
    (X : ℕ → Ω → ℝ) (T : ℕ) (L : ℝ) (hT : 1 ≤ T) (hL : 0 < L)
    (hX : ∀ j ≤ T, StronglyMeasurable[ℱ j] (X j))
    (hbound : ∀ j < T, ∀ᵐ ω ∂μ, |X (j + 1) ω - X j ω| ≤ L)
    (u : ℝ) (hu : 0 < u) (t : ℕ) (ht : t ≤ T) (D : ℝ)
    (hD : ∀ᵐ ω ∂μ, |∑ j ∈ Finset.range t,
      μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω| ≤ D) :
    μ.real {ω | D + u ≤ |X t ω - X 0 ω|} ≤
      2 * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
  apply le_trans (measureReal_le_of_ae_imp ?_)
    (boundedDriftConcentration_proof μ ℱ X T L hT hL hX hbound u hu t ht)
  filter_upwards [hD] with ω hd hω
  have htriangle := abs_add_le (X t ω - X 0 ω - ∑ j ∈ Finset.range t,
    μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω)
    (∑ j ∈ Finset.range t, μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω)
  simp only [sub_add_cancel] at htriangle
  linarith

theorem simultaneous_upper_tail_of_drift_bound
    {ι : Type*} [Fintype ι] (X : ι → ℕ → Ω → ℝ)
    (T : ℕ) (L : ℝ) (hT : 1 ≤ T) (hL : 0 < L)
    (hX : ∀ i j, j ≤ T → StronglyMeasurable[ℱ j] (X i j))
    (hbound : ∀ i j, j < T → ∀ᵐ ω ∂μ, |X i (j + 1) ω - X i j ω| ≤ L)
    (u : ℝ) (hu : 0 < u) (D : ι → ℕ → ℝ)
    (hD : ∀ i t, t ≤ T → ∀ᵐ ω ∂μ, (∑ j ∈ Finset.range t,
      μ[fun ω ↦ X i (j + 1) ω - X i j ω | ℱ j] ω) ≤ D i t) :
    μ.real {ω | ∃ i t, t ≤ T ∧ D i t + u ≤ X i t ω - X i 0 ω} ≤
      2 * Fintype.card ι * (T + 1 : ℕ) * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
  let E : ι × Fin (T + 1) → Set Ω := fun p ↦
    {ω | D p.1 p.2 + u ≤ X p.1 p.2 ω - X p.1 0 ω}
  have heq : {ω | ∃ i t, t ≤ T ∧ D i t + u ≤ X i t ω - X i 0 ω} = ⋃ p, E p := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨i, t, ht, hω⟩
      exact ⟨⟨i, ⟨t, Nat.lt_succ_iff.mpr ht⟩⟩, hω⟩
    · rintro ⟨⟨i, t⟩, hω⟩
      exact ⟨i, t, Nat.lt_succ_iff.mp t.isLt, hω⟩
  rw [heq]
  calc
    μ.real (⋃ p, E p) ≤ ∑ p, μ.real (E p) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _p : ι × Fin (T + 1), 2 * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact upper_tail_of_accumulated_drift_bound (X p.1) T L hT hL
        (hX p.1) (hbound p.1) u hu p.2 (Nat.lt_succ_iff.mp p.2.isLt)
        (D p.1 p.2) (hD p.1 p.2 (Nat.lt_succ_iff.mp p.2.isLt))
    _ = _ := by simp; ring

theorem simultaneous_abs_tail_of_drift_bound
    {ι : Type*} [Fintype ι] (X : ι → ℕ → Ω → ℝ)
    (T : ℕ) (L : ℝ) (hT : 1 ≤ T) (hL : 0 < L)
    (hX : ∀ i j, j ≤ T → StronglyMeasurable[ℱ j] (X i j))
    (hbound : ∀ i j, j < T → ∀ᵐ ω ∂μ, |X i (j + 1) ω - X i j ω| ≤ L)
    (u : ℝ) (hu : 0 < u) (D : ι → ℕ → ℝ)
    (hD : ∀ i t, t ≤ T → ∀ᵐ ω ∂μ, |∑ j ∈ Finset.range t,
      μ[fun ω ↦ X i (j + 1) ω - X i j ω | ℱ j] ω| ≤ D i t) :
    μ.real {ω | ∃ i t, t ≤ T ∧ D i t + u ≤ |X i t ω - X i 0 ω|} ≤
      2 * Fintype.card ι * (T + 1 : ℕ) * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
  let E : ι × Fin (T + 1) → Set Ω := fun p ↦
    {ω | D p.1 p.2 + u ≤ |X p.1 p.2 ω - X p.1 0 ω|}
  have heq : {ω | ∃ i t, t ≤ T ∧ D i t + u ≤ |X i t ω - X i 0 ω|} = ⋃ p, E p := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨i, t, ht, hω⟩
      exact ⟨⟨i, ⟨t, Nat.lt_succ_iff.mpr ht⟩⟩, hω⟩
    · rintro ⟨⟨i, t⟩, hω⟩
      exact ⟨i, t, Nat.lt_succ_iff.mp t.isLt, hω⟩
  rw [heq]
  calc
    μ.real (⋃ p, E p) ≤ ∑ p, μ.real (E p) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _p : ι × Fin (T + 1), 2 * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact abs_tail_of_accumulated_drift_bound (X p.1) T L hT hL
        (hX p.1) (hbound p.1) u hu p.2 (Nat.lt_succ_iff.mp p.2.isLt)
        (D p.1 p.2) (hD p.1 p.2 (Nat.lt_succ_iff.mp p.2.isLt))
    _ = _ := by simp; ring

end
end Balanced

end OAI
