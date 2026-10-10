import OAI.NumberTheory.Ostmann.QuadraticCenter.CutoffBounds

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

def correlationCutoffWeight (c c' s : ℝ) : ℂ :=
  cutoffFourier (c * s) * conj (cutoffFourier (c' * s))

theorem norm_correlationCutoffWeight_le (c c' s : ℝ) :
    ‖correlationCutoffWeight c c' s‖ ≤ cutoffFourierBound ^ 2 := by
  unfold correlationCutoffWeight
  rw [norm_mul, Complex.norm_conj, pow_two]
  exact mul_le_mul (norm_cutoff_fourier_le _) (norm_cutoff_fourier_le _)
    (norm_nonneg _) cutoffFourierBound_pos.le

theorem cutoffFourier_product_sub_le (x y x' y' : ℝ) :
    ‖cutoffFourier x * conj (cutoffFourier x') -
        cutoffFourier y * conj (cutoffFourier y')‖ ≤
      cutoffFourierBound ^ 2 * (|x - y| + |x' - y'|) := by
  have hid : cutoffFourier x * conj (cutoffFourier x') -
      cutoffFourier y * conj (cutoffFourier y') =
      (cutoffFourier x - cutoffFourier y) * conj (cutoffFourier x') +
        cutoffFourier y * conj (cutoffFourier x' - cutoffFourier y') := by
    rw [map_sub]
    ring
  rw [hid]
  calc
    _ ≤ ‖(cutoffFourier x - cutoffFourier y) * conj (cutoffFourier x')‖ +
        ‖cutoffFourier y * conj (cutoffFourier x' - cutoffFourier y')‖ := norm_add_le _ _
    _ ≤ (cutoffFourierBound * |x-y|) * cutoffFourierBound +
        cutoffFourierBound * (cutoffFourierBound * |x'-y'|) := by
      simp only [norm_mul, Complex.norm_conj]
      apply add_le_add
      · exact mul_le_mul (cutoff_fourier_lipschitz x y) (norm_cutoff_fourier_le x')
          (norm_nonneg _) (mul_nonneg cutoffFourierBound_pos.le (abs_nonneg _))
      · exact mul_le_mul (norm_cutoff_fourier_le y) (cutoff_fourier_lipschitz x' y')
          (norm_nonneg _) cutoffFourierBound_pos.le
    _ = _ := by ring

theorem correlationCutoffWeight_sub_le (c c' s t : ℝ) :
    ‖correlationCutoffWeight c c' s - correlationCutoffWeight c c' t‖ ≤
      cutoffFourierBound ^ 2 * (|c| + |c'|) * |s - t| := by
  have h := cutoffFourier_product_sub_le (c*s) (c*t) (c'*s) (c'*t)
  unfold correlationCutoffWeight
  convert h using 1
  rw [← mul_sub, ← mul_sub, abs_mul, abs_mul]
  ring

theorem correlationCutoffWeight_variation_le (c c' start : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      ‖correlationCutoffWeight c c' (start + n) -
        correlationCutoffWeight c c' (start + (n + 1 : ℕ))‖) ≤
      cutoffFourierBound ^ 2 * (|c| + |c'|) * N := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, cutoffFourierBound ^ 2 * (|c| + |c'|) := by
      apply Finset.sum_le_sum
      intro n _
      have h := correlationCutoffWeight_sub_le c c' (start + n) (start + (n+1:ℕ))
      have he : |(start + (n:ℝ)) - (start + (n+1:ℕ))| = 1 := by
        rw [Nat.cast_add, Nat.cast_one]
        have : (start + (n:ℝ)) - (start + ((n:ℝ)+1)) = -1 := by ring
        rw [this]
        norm_num
      simpa only [he, mul_one] using h
    _ = _ := by simp [mul_comm]

theorem abs_lt_quarter_of_cutoffFourier_ne_zero {x : ℝ}
    (hx : cutoffFourier x ≠ 0) : |x| < 1 / 4 := by
  by_contra h
  exact hx (SchwartzCutoff.fourier_psi_zero_of_abs_ge (le_of_not_gt h))

theorem correlationCutoffWeight_support {c c' s : ℝ}
    (h : correlationCutoffWeight c c' s ≠ 0) :
    |c*s| < 1/4 ∧ |c'*s| < 1/4 := by
  have hp := mul_ne_zero_iff.mp h
  refine ⟨abs_lt_quarter_of_cutoffFourier_ne_zero hp.1, ?_⟩
  apply abs_lt_quarter_of_cutoffFourier_ne_zero
  intro hz
  apply hp.2
  simp only [hz, map_zero]

end Ostmann.QuadraticCenter

end

end OAI
