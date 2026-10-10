import Mathlib

namespace OAI

/-!
# Integrating finite multiplicity bounds

Finite sums of indicator functions count the sets containing a point. Integrating
these identities converts pointwise multiplicity bounds into estimates for sums
of measures, including bounds expressed directly using finite cardinalities.
-/

namespace RieszRectifiability

open MeasureTheory Set
open scoped ENNReal

theorem finite_indicator_one_sum_eq_card {ι X : Type*} (s : Finset ι) (A : ι → Set X) (x : X)
    [∀ i, Decidable (x ∈ A i)] :
    ∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ≥0∞)) x =
      ((s.filter (fun i => x ∈ A i)).card : ℝ≥0∞) := by
  classical
  calc
    _ = ∑ _i ∈ s.filter (fun i => x ∈ A i), (1 : ℝ≥0∞) := by
      rw [Finset.sum_filter]
      simp only [Set.indicator_apply]
    _ = _ := by simp

theorem lintegral_finite_indicator_multiplicity {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (A : ι → Set X) (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    (∫⁻ x, ∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) =
      ∑ i ∈ s, μ (A i) := by
  rw [lintegral_finsetSum s (fun i hi => measurable_const.indicator (hA i hi))]
  apply Finset.sum_congr rfl
  intro i hi
  exact lintegral_indicator_one (hA i hi)

theorem measure_sum_le_of_indicator_multiplicity {ι κ X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (t : Finset κ) (A : ι → Set X) (B : κ → Set X)
    (T : Set X) (N : ℕ) (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hB : ∀ j ∈ t, MeasurableSet (B j)) (hT : MeasurableSet T)
    (hpoint : ∀ x, (∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ≥0∞)) x) ≤
      (N : ℝ≥0∞) * (T.indicator (fun _ => 1) x +
        ∑ j ∈ t, (B j).indicator (fun _ => 1) x)) :
    ∑ i ∈ s, μ (A i) ≤ (N : ℝ≥0∞) * (μ T + ∑ j ∈ t, μ (B j)) := by
  rw [← lintegral_finite_indicator_multiplicity μ s A hA]
  calc
    _ ≤ ∫⁻ x, (N : ℝ≥0∞) * (T.indicator (fun _ => 1) x +
        ∑ j ∈ t, (B j).indicator (fun _ => 1) x) ∂μ := lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left (measurable_const.indicator hT)]
      have hTone : (∫⁻ x, T.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) = μ T :=
        lintegral_indicator_one hT
      rw [hTone, lintegral_finite_indicator_multiplicity μ t B hB]

theorem measure_sum_le_of_count_multiplicity {ι κ X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (t : Finset κ) (A : ι → Set X) (B : κ → Set X)
    (T : Set X) (N : ℕ) (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hB : ∀ j ∈ t, MeasurableSet (B j)) (hT : MeasurableSet T)
    [∀ x : X, Decidable (x ∈ T)] [∀ i x, Decidable (x ∈ A i)] [∀ j x, Decidable (x ∈ B j)]
    (hpoint : ∀ x, (s.filter (fun i => x ∈ A i)).card ≤
      N * ((if x ∈ T then 1 else 0) + (t.filter (fun j => x ∈ B j)).card)) :
    ∑ i ∈ s, μ (A i) ≤ (N : ℝ≥0∞) * (μ T + ∑ j ∈ t, μ (B j)) := by
  apply measure_sum_le_of_indicator_multiplicity μ s t A B T N hA hB hT
  intro x
  rw [finite_indicator_one_sum_eq_card, finite_indicator_one_sum_eq_card]
  have hb := hpoint x
  by_cases hx : x ∈ T
  · simp only [ite_eq_left hx] at hb
    simp only [Set.indicator_of_mem hx]
    exact_mod_cast hb
  · simp only [ite_eq_right hx] at hb
    simp only [Set.indicator_of_notMem hx]
    exact_mod_cast hb

end RieszRectifiability

end OAI
