import OAI.NumberTheory.Ostmann.ZeroDensity.OrdinaryPrimeIntervals
import OAI.NumberTheory.Ostmann.Arithmetic.WeightedPrimeIntervals

namespace OAI

/-! # Normalizing the cutoff-weighted prime prior

A fixed positive lower bound for the cutoff on an interior unit log
interval gives the required linear normalization cost.
-/

namespace Ostmann

open scoped BigOperators
open Filter

theorem weighted_prime_interval_lower (q a : ℕ) {s t u v : ℝ}
    (hsu : s ≤ u) (hvt : v ≤ t) (w : ℝ → ℝ) (b : ℝ)
    (hw : ∀ y ∈ Set.Ioc s t, 0 ≤ w y)
    (hb : ∀ y ∈ Set.Ioc u v, b ≤ w y) :
    b * reciprocalPrimeInterval q a (Real.exp u) (Real.exp v) ≤
      weightedReciprocalPrimeInterval q a s t w := by
  let I := Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊
  let J := Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊
  have hIJ : I ⊆ J := by
    intro p hp
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hp
    exact Finset.mem_Ioc.mpr
      ⟨(Nat.floor_mono (Real.exp_le_exp.mpr hsu)).trans_lt hlo,
        hhi.trans (Nat.floor_mono (Real.exp_le_exp.mpr hvt))⟩
  unfold reciprocalPrimeInterval weightedReciprocalPrimeInterval
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ p ∈ I, if p.Prime ∧ Nat.ModEq q p a then
        w (Real.log p) * (p : ℝ)⁻¹ else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases h : p.Prime ∧ Nat.ModEq q p a
      · simp only [ite_eq_left h]
        exact mul_le_mul_of_nonneg_right (hb _ (log_mem_of_mem_exp_interval hp))
          (by positivity)
      · simp [h]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hIJ
      intro p hp _
      by_cases h : p.Prime ∧ Nat.ModEq q p a
      · simp only [ite_eq_left h]
        exact mul_nonneg (hw _ (log_mem_of_mem_exp_interval hp)) (by positivity)
      · simp [h]

/-- This applies to a smooth cutoff supported on a two-unit log interval
and bounded below on its central unit interval. All endpoints and weights
may depend on the log center. -/
theorem PublishedProgressionInput.weighted_normalization_bound (P : PublishedProgressionInput) :
    ∀ᶠ u : ℝ in atTop, ∀ (s t : ℝ) (w : ℝ → ℝ) (b : ℝ),
      s ≤ u → u + 1 ≤ t → 0 < b →
      (∀ y ∈ Set.Ioc s t, 0 ≤ w y) →
      (∀ y ∈ Set.Ioc u (u + 1), b ≤ w y) →
      0 < weightedReciprocalPrimeInterval 1 0 s t w ∧
        (weightedReciprocalPrimeInterval 1 0 s t w)⁻¹ ≤ 2 * (u + 1) / b := by
  filter_upwards [P.ordinary_interval_lower, eventually_ge_atTop (1 : ℝ)] with u hu hu1
  intro s t w b hsu hut hb hw hwlower
  have hdom := weighted_prime_interval_lower 1 0 hsu hut w b hw hwlower
  have hlower : b / (2 * (u + 1)) ≤ weightedReciprocalPrimeInterval 1 0 s t w := by
    have hscaled : b / (2 * (u + 1)) ≤
        b * reciprocalPrimeInterval 1 0 (Real.exp u) (Real.exp (u + 1)) := by
      simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hu hb.le
    exact hscaled.trans hdom
  have hpos : 0 < b / (2 * (u + 1)) := div_pos hb (by positivity)
  refine ⟨hpos.trans_le hlower, ?_⟩
  have hi := one_div_le_one_div_of_le hpos hlower
  simpa only [one_div, inv_div] using hi

end Ostmann

end OAI
