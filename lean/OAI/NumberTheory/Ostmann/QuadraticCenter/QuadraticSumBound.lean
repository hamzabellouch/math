import OAI.NumberTheory.Ostmann.QuadraticCenter.CutoffBounds

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators FourierTransform

def cutoffMultiples (P : ℕ) (N : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊N⌋₊).filter (fun w => P ∣ w)

theorem cutoffMultiples_card_le {P : ℕ} {N : ℝ} (hN : 0 ≤ N) :
    ((cutoffMultiples P N).card : ℝ) ≤ N / P := by
  unfold cutoffMultiples
  rw [Nat.Ioc_filter_dvd_card_eq_div]
  exact Nat.cast_div_le.trans (div_le_div_of_nonneg_right (Nat.floor_le hN) (Nat.cast_nonneg _))

theorem cutoff_fourier_quadratic_zero {N w : ℝ} (hN : 0 < N) (hw : N ≤ w) :
    cutoffFourier ((w / N) ^ 2) = 0 := by
  apply SchwartzCutoff.fourier_psi_zero_of_abs_ge
  have h : 1 ≤ w / N := (le_div_iff₀ hN).mpr (by simpa using hw)
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith

def normalizedSmoothQuadraticSum (P : ℕ) (N : ℝ) (a : ℕ → ℂ) (α : ℝ) : ℂ :=
  ((N⁻¹ : ℝ) : ℂ) * ∑ w ∈ cutoffMultiples P N,
    a w * weylPhase (α * (w : ℝ) ^ 2) * cutoffFourier (((w : ℝ) / N) ^ 2)

theorem normalizedSmoothQuadraticSum_bound {P : ℕ} {N A : ℝ}
    (hN : 0 < N) (hA : 0 ≤ A) (a : ℕ → ℂ) (α : ℝ)
    (ha : ∀ w ∈ cutoffMultiples P N, ‖a w‖ ≤ A) :
    ‖normalizedSmoothQuadraticSum P N a α‖ ≤ A * cutoffFourierBound / P := by
  have hC := cutoffFourierBound_pos.le
  unfold normalizedSmoothQuadraticSum
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hN.le)]
  calc
    _ ≤ N⁻¹ * ∑ w ∈ cutoffMultiples P N,
        ‖a w * weylPhase (α * (w : ℝ) ^ 2) * cutoffFourier (((w : ℝ) / N) ^ 2)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hN.le)
    _ ≤ N⁻¹ * ∑ _w ∈ cutoffMultiples P N, A * cutoffFourierBound := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hN.le)
      apply Finset.sum_le_sum
      intro w hw
      simp only [norm_mul, weylPhase_norm, mul_one]
      exact mul_le_mul (ha w hw) (norm_cutoff_fourier_le _) (norm_nonneg _) hA
    _ = N⁻¹ * ((cutoffMultiples P N).card * (A * cutoffFourierBound)) := by simp
    _ ≤ N⁻¹ * ((N / P) * (A * cutoffFourierBound)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (cutoffMultiples_card_le hN.le) (mul_nonneg hA hC))
        (inv_nonneg.mpr hN.le)
    _ = _ := by field_simp

theorem normalizedSmoothQuadraticSum_truncation {P W : ℕ} {N : ℝ}
    (hN : 0 < N) (hW : ⌊N⌋₊ ≤ W) (a : ℕ → ℂ) (α : ℝ) :
    normalizedSmoothQuadraticSum P N a α =
      ((N⁻¹ : ℝ) : ℂ) * ∑ w ∈ (Finset.Ioc 0 W).filter (fun w => P ∣ w),
        a w * weylPhase (α * (w : ℝ) ^ 2) * cutoffFourier (((w : ℝ) / N) ^ 2) := by
  unfold normalizedSmoothQuadraticSum
  congr 1
  apply Finset.sum_subset
  · intro w hw
    obtain ⟨hw, hp⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
      ⟨(Finset.mem_Ioc.mp hw).1, (Finset.mem_Ioc.mp hw).2.trans hW⟩, hp⟩
  · intro w hw hnot
    obtain ⟨hw, hp⟩ := Finset.mem_filter.mp hw
    have hnotle : ¬w ≤ ⌊N⌋₊ := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hw).1, h⟩, hp⟩)
    have hlt : N < (w : ℝ) := (Nat.floor_lt hN.le).mp (Nat.lt_of_not_ge hnotle)
    rw [cutoff_fourier_quadratic_zero hN hlt.le, mul_zero]

end Ostmann.QuadraticCenter

end

end OAI
