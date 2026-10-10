import OAI.NumberTheory.TwoPoint.Halasz.HalaszDoubleEstimate
import OAI.NumberTheory.TwoPoint.Halasz.HalaszDoubleMean
import OAI.NumberTheory.TwoPoint.Halasz.HalaszNumericalErrors
import OAI.NumberTheory.TwoPoint.Halasz.HalaszSmoothBounds

namespace OAI

/-! An ordinary Halász mean estimate, with an absolute constant and
the logarithmic-height range needed in the MRT argument. -/

namespace TwoPointCorrelations

open Finset Filter

/-- Uniform ordinary mean estimate for completely multiplicative functions.
The distance lower bound is required only for |t| ≤ (log N)^8. -/
theorem halasz_mean_value : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ (N : ℕ), X₀ ≤ N →
    ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ a b, 0 < a → 0 < b → f (a * b) = f a * f b) → OneBounded f →
    ∀ (M : ℝ), 0 ≤ M →
      (∀ t ∈ Set.Icc (-(Real.log (N : ℝ) ^ 8)) (Real.log (N : ℝ) ^ 8),
        M ≤ squaredDistance f (mrtArchimedeanTwist t) N) →
      ‖∑ n ∈ Icc 1 N, f n‖ ≤ C * N *
        ((M + 1) * Real.exp (-M) + Real.log (Real.log N) / Real.log N) := by
  obtain ⟨C₁, B, hC₁, hB, hdouble⟩ := halasz_double_convolution_estimate
  obtain ⟨H₀, hH₀, hEuler⟩ := mrt_smooth_distance_bound
  let H := max 1 H₀
  let D := 2 * C₁ * H + 8 * C₁ + (halaszDoubleErrorConstant + 12)
  let C := 1 + C₁ * H + D
  have hH : 1 ≤ H := le_max_left _ _
  have hH₀H : H₀ ≤ H := le_max_right _ _
  have hD : 0 ≤ D := by
    dsimp [D]
    have := halaszDoubleErrorConstant_nonneg
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (halasz_eventually_numeric_scale B)
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ)))
  refine ⟨C, max X₀ X₁, hC, ?_⟩
  intro N hXN f hf1 hf hbound M hM hdist
  obtain ⟨hNr, hll, hl4, hl16, hBT⟩ := hX₀ N ((le_max_left _ _).trans hXN)
  have hN : 3 ≤ N := by exact_mod_cast hNr
  have hN2 : 2 ≤ N := by omega
  have hℓ2 : 2 ≤ Real.log (N : ℝ) := hX₁ N ((le_max_right _ _).trans hXN)
  have hℓ : 1 ≤ Real.log (N : ℝ) := by linarith
  have hℓ0 : 0 < Real.log (N : ℝ) := by linarith
  have hl4N : Real.log (N : ℝ) ^ 4 ≤ N :=
    (pow_le_pow_right₀ hℓ (by norm_num : (4 : ℕ) ≤ 16)).trans (by linarith)
  let m := ⌈(N : ℝ) / Real.log (N : ℝ) ^ 4⌉₊
  obtain ⟨hm, hmN, _, hml, hmu⟩ := halasz_smoothing_integer hN2 hl4 hl4N
  have hglobal (t : ℝ) :
      ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * Complex.I)‖ ≤
        H * Real.log N := by
    rw [halasz_smooth_LSeries]
    have he := hEuler f hf1 hf hbound N hN2 t
    have hd := halasz_distance_nonneg f hbound N t
    have hx : Real.exp (-squaredDistance f (mrtArchimedeanTwist t) N) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    calc
      _ ≤ H₀ * Real.log N * Real.exp (-squaredDistance f (mrtArchimedeanTwist t) N) := he
      _ ≤ H₀ * Real.log N := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ H₀ * Real.log (N : ℝ))
      _ ≤ H * Real.log N := mul_le_mul_of_nonneg_right hH₀H hℓ0.le
  have hcentral (t : ℝ)
      (ht : t ∈ Set.Icc (-(Real.log (N : ℝ) ^ 8)) (Real.log (N : ℝ) ^ 8)) :
      ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * Complex.I)‖ ≤
        (H * Real.log N) * Real.exp (-M) := by
    rw [halasz_smooth_LSeries]
    apply (hEuler f hf1 hf hbound N hN2 t).trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hH₀H hℓ0.le
    · exact Real.exp_le_exp.mpr (neg_le_neg (hdist t ht))
    · positivity
    · positivity
  have hb := hdouble f hf1 hf hbound N m (Real.log N ^ 16) (Real.log N ^ 8)
    (H * Real.log N) (H * Real.log N) M hN2 hm hmN
    (one_le_pow₀ hℓ) (by rw [← pow_mul]) hBT
    (le_mul_of_one_le_left hℓ0.le hH) (by positivity) hM hcentral hglobal
  have herr := halasz_numerical_errors hN hC₁.le (by linarith : 0 ≤ H) hℓ hm hml hmu
  have hreduce := halasz_double_mean_log_sixteenth f hbound hf N hll (one_le_pow₀ hℓ) hl16
  have hsmall : (2 * C₁ * H + 8 * C₁) * N ≤
      (2 * C₁ * H + 8 * C₁) * N * Real.log (Real.log N) :=
    le_mul_of_one_le_right (by positivity) hll
  have hmain : Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      C₁ * N * (H * Real.log N) * (M + 1) * Real.exp (-M) +
        D * N * Real.log (Real.log N) := by
    dsimp [D]
    linarith
  have hdiv := div_le_div_of_nonneg_right hmain hℓ0.le
  have heq : (C₁ * N * (H * Real.log N) * (M + 1) * Real.exp (-M) +
      D * N * Real.log (Real.log N)) / Real.log N =
      C₁ * H * N * ((M + 1) * Real.exp (-M)) +
        D * N * (Real.log (Real.log N) / Real.log N) := by
    field_simp
  rw [mul_div_cancel_left₀ _ hℓ0.ne', heq] at hdiv
  have hC₁H : C₁ * H ≤ C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith [show 0 ≤ C₁ * H by positivity]
  calc
    _ ≤ C₁ * H * N * ((M + 1) * Real.exp (-M)) +
        D * N * (Real.log (Real.log N) / Real.log N) := hdiv
    _ ≤ C * N * ((M + 1) * Real.exp (-M)) +
        C * N * (Real.log (Real.log N) / Real.log N) := by gcongr
    _ = _ := by ring

end TwoPointCorrelations

end OAI
