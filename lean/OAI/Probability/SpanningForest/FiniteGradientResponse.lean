import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.FiniteGradientResponse

variable {ι : Type*}

def segmentField (h k : ι → ℝ) (t : ℝ) : ι → ℝ :=
  fun i => h i + t * (k i - h i)

@[simp] theorem segmentField_zero (h k : ι → ℝ) : segmentField h k 0 = h := by
  funext i
  simp [segmentField]

@[simp] theorem segmentField_one (h k : ι → ℝ) : segmentField h k 1 = k := by
  funext i
  simp [segmentField]

theorem abs_sum_mul_le (E : Finset ι) (row direction : ι → ℝ)
    (L D : ℝ) (hD : 0 ≤ D)
    (hrow : (∑ i ∈ E, |row i|) ≤ L)
    (hdir : ∀ i ∈ E, |direction i| ≤ D) :
    |∑ i ∈ E, row i * direction i| ≤ L * D := by
  calc
    |∑ i ∈ E, row i * direction i| ≤ ∑ i ∈ E, |row i * direction i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ E, |row i| * D := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hdir i hi) (abs_nonneg _)
    _ = (∑ i ∈ E, |row i|) * D := (Finset.sum_mul _ _ _).symm
    _ ≤ L * D := mul_le_mul_of_nonneg_right hrow hD

theorem response_le_of_line_derivative (E : Finset ι)
    (p : (ι → ℝ) → ℝ) (row : (ι → ℝ) → ι → ℝ)
    (h k : ι → ℝ) (L D : ℝ) (hD : 0 ≤ D)
    (hdir : ∀ i ∈ E, |k i - h i| ≤ D)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => p (segmentField h k s))
        (∑ i ∈ E, row (segmentField h k t) i * (k i - h i)) t)
    (hrow : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      (∑ i ∈ E, |row (segmentField h k t) i|) ≤ L) :
    |p k - p h| ≤ L * D := by
  have hbound : ‖p (segmentField h k 1) - p (segmentField h k 0)‖ ≤ L * D := by
    apply norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := fun s => p (segmentField h k s))
      (f' := fun t => ∑ i ∈ E, row (segmentField h k t) i * (k i - h i))
    · intro t ht
      exact (hderiv t ht).hasDerivWithinAt
    · intro t ht
      simpa only [Real.norm_eq_abs] using
        abs_sum_mul_le E (row (segmentField h k t)) (fun i => k i - h i)
          L D hD (hrow t ht) hdir
  simpa only [segmentField_one, segmentField_zero, Real.norm_eq_abs] using hbound

end Problem336.FiniteGradientResponse

end

end OAI
