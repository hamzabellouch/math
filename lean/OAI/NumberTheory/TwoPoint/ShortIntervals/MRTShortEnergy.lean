import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWindowTransfer

namespace OAI

/-! The normalized fixed-h Fourier estimate, in the usual low/high
frequency kernel, and its exact finite Dirichlet-polynomial form. -/

namespace TwoPointCorrelations

open MeasureTheory Finset Set
open scoped Classical

noncomputable def mrtShortKernel (T t : ℝ) : ℝ :=
  min 1 (T^2/(1+t^2))

lemma mrt_short_kernel_integrable (S : Finset ℕ) (a : ℕ → ℂ) (T : ℝ) :
    Integrable (fun t => mrtShortKernel T t * ‖mrtLogDirichlet S a t‖^2) := by
  let C := ∑ n ∈ S, ‖a n‖ * Real.exp (-Real.log (n:ℝ))
  have hm : Measurable (fun t => mrtShortKernel T t * ‖mrtLogDirichlet S a t‖^2) := by
    unfold mrtShortKernel mrtLogDirichlet
    fun_prop
  apply (integrable_inv_one_add_sq.const_mul (T^2*C^2)).mono' hm.aestronglyMeasurable
  filter_upwards with t
  have hn : 0 ≤ mrtShortKernel T t := le_min (by norm_num) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hn (sq_nonneg _))]
  calc
    _ ≤ (T^2/(1+t^2))*C^2 := mul_le_mul (min_le_right _ _)
      (pow_le_pow_left₀ (norm_nonneg _) (mrt_log_dirichlet_norm S a t) 2)
      (sq_nonneg _) (by positivity)
    _ = _ := by ring

lemma mrt_scaled_window_kernel {N h : ℝ} (hN : 0 < N) (hh : 0 < h) (t : ℝ) :
    (N/h)^2 * mrtWindowKernel (3*h/N) t ≤ 144 * mrtShortKernel (N/h) t := by
  have he : (N/h)^2 * (16*(3*h/N)^2) = 144 := by field_simp; ring
  have h₁ : (N/h)^2 * mrtWindowKernel (3*h/N) t ≤ 144 := by
    rw [← he]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (sq_nonneg _)
  have h₂ : (N/h)^2 * mrtWindowKernel (3*h/N) t ≤
      144 * ((N/h)^2/(1+t^2)) := by
    calc
      _ ≤ (N/h)^2 * (25/(1+t^2)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg _)
      _ ≤ _ := by
        have hp : 0 ≤ (N/h)^2/(1+t^2) := by positivity
        calc
          _ = 25*((N/h)^2/(1+t^2)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num : (25:ℝ) ≤ 144) hp
  unfold mrtShortKernel
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 144), mul_one]
  exact le_min h₁ h₂

theorem mrt_normalized_short_energy (S : Finset ℕ) (hn : ∀ n ∈ S, 0 < n)
    (a : ℕ → ℂ) {N h : ℝ} (hN : 0 < N) (hh : 0 < h) (hhN : h ≤ N) :
    (∫ x in N..2*N, ‖mrtIntervalSum S a x h‖^2) / (N*h^2) ≤
      (69984/(2*Real.pi)) *
        ∫ t : ℝ, mrtShortKernel (N/h) t * ‖mrtLogDirichlet S a t‖^2 := by
  have hbase := mrt_fixed_window_fourier_energy S hn a hN hh hhN
  have hk := integral_mono
    ((mrt_window_kernel_integrable S a (3*h/N)).const_mul ((N/h)^2))
    ((mrt_short_kernel_integrable S a (N/h)).const_mul 144) (fun t => by
      change (N/h)^2 * (mrtWindowKernel (3*h/N) t * ‖mrtLogDirichlet S a t‖^2) ≤
        144 * (mrtShortKernel (N/h) t * ‖mrtLogDirichlet S a t‖^2)
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (mrt_scaled_window_kernel hN hh t) (sq_nonneg _))
  rw [integral_const_mul, integral_const_mul] at hk
  calc
    _ ≤ ((486*N^3/(2*Real.pi)) *
        ∫ t : ℝ, mrtWindowKernel (3*h/N) t * ‖mrtLogDirichlet S a t‖^2) / (N*h^2) :=
      div_le_div_of_nonneg_right hbase (by positivity)
    _ = (486/(2*Real.pi)) * (((N/h)^2) *
        ∫ t : ℝ, mrtWindowKernel (3*h/N) t * ‖mrtLogDirichlet S a t‖^2) := by
      field_simp
    _ ≤ (486/(2*Real.pi)) * (144 *
        ∫ t : ℝ, mrtShortKernel (N/h) t * ‖mrtLogDirichlet S a t‖^2) :=
      mul_le_mul_of_nonneg_left hk (by positivity)
    _ = _ := by ring

lemma mrt_log_dirichlet_polynomial (S : Finset ℕ) (hn : ∀ n ∈ S, 0 < n)
    (a : ℕ → ℂ) (t : ℝ) :
    mrtLogDirichlet S a t =
      mrtExponentialPolynomial S (fun n => a n/(n:ℂ))
        (fun n => -Real.log (n:ℝ)) t := by
  unfold mrtLogDirichlet mrtExponentialPolynomial
  apply sum_congr rfl
  intro n hnS
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn n hnS
  have he : -((1:ℂ)+(t:ℂ)*Complex.I)*(Real.log (n:ℝ):ℂ) =
      ((-Real.log (n:ℝ):ℝ):ℂ) + ((-Real.log (n:ℝ)*t:ℝ):ℂ)*Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hn0]
  push_cast
  ring

end TwoPointCorrelations

end OAI
