import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.InheritedHeightTail

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem normalized_second_moment_bound {d : ℕ}
    (μ : Measure (Ambient d)) (u : Ambient d → ℝ) (δ D : ℝ) (hδ : 0 < δ)
    (hbound : (∫ x, u x ^ 2 ∂μ) ≤ δ ^ 2 * D) :
    (∫ x, (u x / δ) ^ 2 ∂μ) ≤ D := by
  simp only [div_pow, integral_div]
  exact (div_le_iff₀ (sq_pos_of_pos hδ)).mpr (by simpa only [mul_comm D] using! hbound)

theorem dyadic_second_moment_rescale (m q k : ℕ) (D b R : ℝ) (hR : 0 < R) :
    ((D * ((2 : ℝ) ^ q) ^ m * ((2 : ℝ) ^ q * b ^ q) ^ 2) / R ^ (m + 2)) *
        (R * 2 ^ k) ^ m * ((R * 2 ^ k) * b ^ k) ^ 2 =
      D * ((2 : ℝ) ^ (q + k)) ^ m * ((2 : ℝ) ^ (q + k) * b ^ (q + k)) ^ 2 := by
  rw [pow_add R m 2]
  simp only [pow_add, mul_pow]
  field_simp

theorem comparable_ball_moments_from_dyadic_control {d : ℕ} (m : ℕ)
    (μ : ℕ → Measure (Ambient d)) (a : Ambient d) (w : ℕ → Ambient d → ℝ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ)
    (hw : ∀ l j, MemLp (w j) 2 ((μ j).restrict (ball a ((2 : ℝ) ^ l))))
    (hbound : ∀ j l, l ≤ N j → (∫ x in ball a ((2 : ℝ) ^ l), w j x ^ 2 ∂μ j) ≤
      D * ((2 : ℝ) ^ l) ^ m * ((2 : ℝ) ^ l * b ^ l) ^ 2)
    (T R Bmin : ℝ) (hR : 0 < R) :
    ∃ B : ℝ, Bmin ≤ B ∧
      (∀ k j, MemLp (w j) 2 ((μ j).restrict (ball a (T * (2 : ℝ) ^ k)))) ∧
      ∀ k, ∀ᶠ j in atTop,
        (∫ x in ball a (T * (2 : ℝ) ^ k), w j x ^ 2 ∂μ j) ≤
          (B * (R * 2 ^ k) ^ m) * ((R * 2 ^ k) * b ^ k) ^ 2 := by
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt T (by norm_num : (1 : ℝ) < 2)
  let B₀ := (D * ((2 : ℝ) ^ q) ^ m * ((2 : ℝ) ^ q * b ^ q) ^ 2) / R ^ (m + 2)
  let B := max Bmin B₀
  have hrad : ∀ k, T * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (q + k) := by
    intro k
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right hq.le (by positivity)
  have hμ : ∀ k j, (μ j).restrict (ball a (T * (2 : ℝ) ^ k)) ≤
      (μ j).restrict (ball a ((2 : ℝ) ^ (q + k))) :=
    fun k j => Measure.restrict_mono (ball_subset_ball (hrad k)) le_rfl
  refine ⟨B, le_max_left _ _, fun k j => MemLp.mono_measure (hμ k j) (hw (q + k) j), ?_⟩
  intro k
  filter_upwards [hN.eventually (eventually_ge_atTop (q + k))] with j hj
  calc
    _ ≤ ∫ x in ball a ((2 : ℝ) ^ (q + k)), w j x ^ 2 ∂μ j :=
      integral_mono_measure (hμ k j) (Eventually.of_forall (fun x => sq_nonneg (w j x)))
        (hw (q + k) j).integrable_sq
    _ ≤ D * ((2 : ℝ) ^ (q + k)) ^ m * ((2 : ℝ) ^ (q + k) * b ^ (q + k)) ^ 2 :=
      hbound j (q + k) hj
    _ = (B₀ * (R * 2 ^ k) ^ m) * ((R * 2 ^ k) * b ^ k) ^ 2 :=
      (dyadic_second_moment_rescale m q k D b R hR).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right Bmin B₀) (by positivity)) (sq_nonneg _)

end

end RieszRectifiability

end OAI
