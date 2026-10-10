import OAI.NumberTheory.CubicMoment.Estimates.LogEndpoint

namespace OAI

/-!
# The sharp-cutoff error at integer norms

The smoothing constructed from the fixed Fourier kernel has a summable
endpoint error.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

def smoothLogInterval (T v : ℝ) : ℂ :=
  intervalSmoothing (scaledKernel truncationKernel T) 0 (Real.log 2) (Real.log v)

def sharpIntervalError (X T n : ℝ) : ℂ :=
  (intervalStep X (2*X) n : ℂ) - smoothLogInterval T (n/X)

theorem intervalStep_log {v : ℝ} (hv : 0 < v) :
    intervalStep 0 (Real.log 2) (Real.log v) = intervalStep 1 2 v := by
  have he : Real.log v ∈ Set.Icc 0 (Real.log 2) ↔ v ∈ Set.Icc 1 2 := by
    rw [Set.mem_Icc, Set.mem_Icc, ← Real.log_one]
    exact and_congr (Real.log_le_log_iff (by norm_num) hv)
      (Real.log_le_log_iff hv (by norm_num))
  simp only [intervalStep, he]

theorem intervalStep_div {X n : ℝ} (hX : 0 < X) :
    intervalStep 1 2 (n/X) = intervalStep X (2*X) n := by
  simp only [intervalStep, Set.mem_Icc, le_div_iff₀ hX, div_le_iff₀ hX, one_mul]

theorem kernelMoment_nonneg (k : ℝ → ℂ) (T : ℝ) : 0 ≤ kernelMoment k T :=
  integral_nonneg (fun _ => mul_nonneg (_root_.norm_nonneg _) (sq_nonneg _))

/-- The concrete error has the two summable endpoint majorants. -/
theorem sharpIntervalError_bound {X T n : ℝ}
    (hX : 0 < X) (hT : 0 < T) (hn : 0 < n) (hn4 : n ≤ 4*X) :
    ‖sharpIntervalError X T n‖ ≤ 16 * kernelMoment truncationKernel 1 *
      (endpointKernel (X/T) (n-X) + endpointKernel (X/T) (n-2*X)) := by
  have h := fourier_interval_error hT 0 (Real.log 2) (Real.log (n/X))
  rw [intervalStep_log (div_pos hn hX), intervalStep_div hX] at h
  have h₁ := log_boundary_le_endpoint hX hT hn hn4
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 4)
  have h₂ := log_boundary_le_endpoint hX hT hn hn4
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 4)
  simp only [Real.log_one, sub_zero, one_mul] at h₁
  simp only [sub_zero] at h
  have hM := kernelMoment_nonneg truncationKernel 1
  calc
    _ ≤ kernelMoment truncationKernel 1 / (1 + T*|Real.log (n/X)|)^2 +
        kernelMoment truncationKernel 1 / (1 + T*|Real.log (n/X)-Real.log 2|)^2 := h
    _ ≤ kernelMoment truncationKernel 1 * (16 * endpointKernel (X/T) (n-X)) +
        kernelMoment truncationKernel 1 * (16 * endpointKernel (X/T) (n-2*X)) := by
      simpa only [← mul_div_assoc, mul_one] using add_le_add
        (mul_le_mul_of_nonneg_left h₁ hM) (mul_le_mul_of_nonneg_left h₂ hM)
    _ = _ := by ring

/-- Collected integer coefficients incur exactly the permitted truncation cost. -/
theorem sharp_interval_sum_error {X T M : ℝ} (hX : 0 < X) (hT : 0 < T)
    (hM : 0 ≤ M) (s : Finset ℤ) (c : ℤ → ℂ)
    (hs : ∀ n ∈ s, 0 < (n : ℝ) ∧ (n : ℝ) ≤ 4*X)
    (hc : ∀ n ∈ s, ‖c n‖ ≤ M) :
    ‖∑ n ∈ s, c n * sharpIntervalError X T n‖ ≤
      64 * kernelMoment truncationKernel 1 * M * (1 + X/T) := by
  have h := weighted_endpoint_error (div_pos hX hT)
    (mul_nonneg (by norm_num) (kernelMoment_nonneg truncationKernel 1)) hM
    s X (2*X) c (fun n => sharpIntervalError X T n) hc
    (fun n hn => sharpIntervalError_bound hX hT (hs n hn).1 (hs n hn).2)
  convert h using 1
  ring

/-- At the chosen height, the actual Fourier-smoothing error is little-oh
of the Patterson first-moment scale. -/
theorem sharp_interval_error_isLittleO {ε ρ : ℝ} (hερ : ε < ρ) (hρ : ρ ≤ 5/6)
    (s : ℝ → Finset ℤ) (c : ℝ → ℤ → ℂ)
    (hs : ∀ X : ℝ, 1 ≤ X → ∀ n ∈ s X, 0 < (n : ℝ) ∧ (n : ℝ) ≤ 4*X)
    (hc : ∀ X : ℝ, 1 ≤ X → ∀ n ∈ s X, ‖c X n‖ ≤ X^ε) :
    (fun X : ℝ => ∑ n ∈ s X, c X n *
      sharpIntervalError X (X^(1/6+ρ : ℝ)) n)
      =o[Filter.atTop] firstMomentScale := by
  apply endpoint_error_isLittleO (C := 16 * kernelMoment truncationKernel 1) hερ hρ
    (mul_nonneg (by norm_num) (kernelMoment_nonneg truncationKernel 1)) s c _ hc
  intro X hX n hn
  have hX0 : 0 < X := by linarith
  exact sharpIntervalError_bound hX0 (Real.rpow_pos_of_pos hX0 _) (hs X hX n hn).1
    (hs X hX n hn).2

end CubicFirstMoment

end

end OAI
