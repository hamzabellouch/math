import OAI.Probability.SpanningForest.ExponentialFamily
import OAI.Probability.SpanningForest.FiniteGradientResponse

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.TiltResponse

open ExponentialFamily

variable {α ι : Type*} [Fintype α]

def cov (w g f q : α → ℝ) (t : ℝ) : ℝ :=
  mean w g (fun a => f a * q a) t - mean w g f t * mean w g q t

lemma mean_const_mul (w g f : α → ℝ) (r t : ℝ) :
    mean w g (fun a => r * f a) t = r * mean w g f t := by
  simp only [mean_eq_sum_mass]
  simp_rw [show ∀ a, mass w g t a * (r * f a) = r * (mass w g t a * f a)
    by intro a; ring]
  exact (Finset.mul_sum _ _ _).symm

lemma mean_sum (E : Finset ι) (w g : α → ℝ) (f : ι → α → ℝ) (t : ℝ) :
    mean w g (fun a => ∑ i ∈ E, f i a) t = ∑ i ∈ E, mean w g (f i) t := by
  simp only [mean_eq_sum_mass, Finset.mul_sum]
  exact Finset.sum_comm

lemma cov_const_mul_right (w g f q : α → ℝ) (r t : ℝ) :
    cov w g f (fun a => r * q a) t = r * cov w g f q t := by
  unfold cov
  simp_rw [show ∀ a, f a * (r * q a) = r * (f a * q a) by intro a; ring]
  rw [mean_const_mul, mean_const_mul]
  ring

lemma cov_sum_right (E : Finset ι) (w g f : α → ℝ) (q : ι → α → ℝ) (t : ℝ) :
    cov w g f (fun a => ∑ i ∈ E, q i a) t = ∑ i ∈ E, cov w g f (q i) t := by
  simp only [cov, Finset.mul_sum]
  rw [mean_sum, mean_sum, Finset.mul_sum, Finset.sum_sub_distrib]

theorem mean_sub_le_of_cov_le (w g f : α → ℝ) (L : ℝ)
    (hZ : ∀ t ∈ Set.Icc (0 : ℝ) 1, partition w g t ≠ 0)
    (hcov : ∀ t ∈ Set.Ico (0 : ℝ) 1, |cov w g f g t| ≤ L) :
    |mean w g f 1 - mean w g f 0| ≤ L := by
  rw [← Real.norm_eq_abs]
  apply norm_image_sub_le_of_norm_deriv_le_segment_01'
  · intro t ht
    exact (hasDerivAt_mean w g f t (hZ t ht)).hasDerivWithinAt
  · intro t ht
    simpa only [Real.norm_eq_abs, cov] using hcov t ht

theorem cov_direction_le (E : Finset ι) (w g f : α → ℝ)
    (x : ι → α → ℝ) (direction : ι → ℝ) (t L D : ℝ)
    (hD : 0 ≤ D) (hdir : ∀ i ∈ E, |direction i| ≤ D)
    (hrow : (∑ i ∈ E, |cov w g f (x i) t|) ≤ L) :
    |cov w g f (fun a => ∑ i ∈ E, direction i * x i a) t| ≤ L * D := by
  rw [cov_sum_right]
  simp_rw [cov_const_mul_right, mul_comm (direction _)]
  exact FiniteGradientResponse.abs_sum_mul_le E (fun i => cov w g f (x i) t)
    direction L D hD hrow hdir

theorem mean_sub_le_of_covariance_row (E : Finset ι) (w f : α → ℝ)
    (x : ι → α → ℝ) (direction : ι → ℝ) (L D : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hpos : ∃ a, 0 < w a)
    (hD : 0 ≤ D) (hdir : ∀ i ∈ E, |direction i| ≤ D)
    (hrow : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      (∑ i ∈ E, |cov w (fun a => ∑ j ∈ E, direction j * x j a) f (x i) t|) ≤ L) :
    |mean w (fun a => ∑ i ∈ E, direction i * x i a) f 1 -
      mean w (fun a => ∑ i ∈ E, direction i * x i a) f 0| ≤ L * D := by
  apply mean_sub_le_of_cov_le
  · intro t _
    exact ne_of_gt (partition_pos w _ t hw hpos)
  · intro t ht
    exact cov_direction_le E w _ f x direction t L D hD hdir (hrow t ht)

end Problem336.TiltResponse

end

end OAI
