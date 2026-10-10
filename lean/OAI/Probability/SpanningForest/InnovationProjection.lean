import Mathlib

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem336.InnovationProjection

theorem abs_scalar_correction_le
    {u v x : ℝ} {b : ℝ → ℝ} (huv : u ≤ v)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hb : IntervalIntegrable b volume u v)
    (hb0 : ∀ t ∈ Set.Icc u v, 0 ≤ b t)
    (hb1 : ∀ t ∈ Set.Icc u v, b t ≤ 1) :
    |(v - u) * x - ∫ t in u..v, b t| ≤ v - u := by
  have hnonneg : 0 ≤ ∫ t in u..v, b t := intervalIntegral.integral_nonneg huv hb0
  have hupper : (∫ t in u..v, b t) ≤ v - u := by
    have h := intervalIntegral.integral_mono_on huv hb
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume u v) hb1
    simpa using h
  have htime : 0 ≤ v - u := sub_nonneg.mpr huv
  have hsignal0 := mul_nonneg htime hx0
  have hsignal1 : (v - u) * x ≤ v - u := by
    simpa using mul_le_mul_of_nonneg_left hx1 htime
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_finite_correction_le {I : Type*} (s : Finset I)
    (θ x : I → ℝ) (b : I → ℝ → ℝ) {u v : ℝ} (huv : u ≤ v)
    (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1)
    (hb : ∀ i ∈ s, IntervalIntegrable (b i) volume u v)
    (hbrange : ∀ i ∈ s, ∀ t ∈ Set.Icc u v, 0 ≤ b i t ∧ b i t ≤ 1) :
    |∑ i ∈ s, θ i * ((v - u) * x i - ∫ t in u..v, b i t)| ≤
      (v - u) * ∑ i ∈ s, |θ i| := by
  calc
    _ ≤ ∑ i ∈ s, |θ i * ((v - u) * x i - ∫ t in u..v, b i t)| := by
      simpa only [Real.norm_eq_abs] using
        norm_sum_le s (fun i => θ i * ((v - u) * x i - ∫ t in u..v, b i t))
    _ ≤ ∑ i ∈ s, |θ i| * (v - u) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact abs_scalar_correction_le huv (hx i hi).1 (hx i hi).2 (hb i hi)
        (fun t ht => (hbrange i hi t ht).1) (fun t ht => (hbrange i hi t ht).2)
    _ = (v - u) * ∑ i ∈ s, |θ i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem scalar_increment_decomposition (x : ℝ) (B b : ℝ → ℝ) (u v : ℝ)
    (h0u : IntervalIntegrable b volume 0 u)
    (huv : IntervalIntegrable b volume u v) :
    (v * x + B v - ∫ t in (0 : ℝ)..v, b t) -
      (u * x + B u - ∫ t in (0 : ℝ)..u, b t) =
      (B v - B u) + ((v - u) * x - ∫ t in u..v, b t) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals h0u huv]
  ring

theorem finite_increment_decomposition {I : Type*} (s : Finset I)
    (θ x : I → ℝ) (B b : I → ℝ → ℝ) (u v : ℝ)
    (h0u : ∀ i ∈ s, IntervalIntegrable (b i) volume 0 u)
    (huv : ∀ i ∈ s, IntervalIntegrable (b i) volume u v) :
    (∑ i ∈ s, θ i *
      ((v * x i + B i v - ∫ t in (0 : ℝ)..v, b i t) -
       (u * x i + B i u - ∫ t in (0 : ℝ)..u, b i t))) =
      (∑ i ∈ s, θ i * (B i v - B i u)) +
      (∑ i ∈ s, θ i * ((v - u) * x i - ∫ t in u..v, b i t)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [scalar_increment_decomposition (x i) (B i) (b i) u v (h0u i hi) (huv i hi)]
  ring

end Problem336.InnovationProjection

end

end OAI
