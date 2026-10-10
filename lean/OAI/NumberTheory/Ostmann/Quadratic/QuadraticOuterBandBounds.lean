import OAI.NumberTheory.Ostmann.Quadratic.QuadraticNormalizedGauss
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionWeights

namespace OAI

/-! # Both outer divisor corrections with their original coefficient norms -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_low_correction_weight (F : ℕ → ℕ → ℂ) (D B : ℕ) (V : ℝ) :
    ‖∑ d ∈ (Finset.Ioc D (2 * D)).filter (fun d : ℕ => (d : ℝ) ≤ V),
      ∑ b ∈ (oddSquarefreeRange (2 * B)).filter (fun b => B ≤ b),
        (ArithmeticFunction.moebius d : ℂ) * F d b‖ ≤
      ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B), ‖F d b‖ := by
  let S := (Finset.Ioc D (2 * D)).filter (fun d : ℕ => (d : ℝ) ≤ V)
  let R := (oddSquarefreeRange (2 * B)).filter (fun b => B ≤ b)
  calc
    _ ≤ ∑ d ∈ S, ∑ b ∈ R, ‖(ArithmeticFunction.moebius d : ℂ) * F d b‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ d ∈ S, ∑ b ∈ R, ‖F d b‖ := by
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum
      intro b _
      have hμ : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      rw [norm_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hμ (norm_nonneg (F d b))
    _ ≤ _ := by
      apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
        (fun d _ _ => Finset.sum_nonneg (fun b _ => norm_nonneg _))).trans
      exact Finset.sum_le_sum (fun d _ =>
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (fun b _ _ => norm_nonneg _))

theorem quadratic_low_correction_band_bound (B N D : ℕ) (hN : 0 < N) (V : ℝ)
    (v w : ℕ → ℂ) (hv : ∀ n < N, v n = 0) (hw : ∀ n < N, w n = 0)
    (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ j) (K₂ j))
    (hcost : ∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) v) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) w) ≤ T) :
    ‖∑ d ∈ (Finset.Ioc D (2 * D)).filter (fun d : ℕ => (d : ℝ) ≤ V),
      ∑ b ∈ (oddSquarefreeRange (2 * B)).filter (fun b => B ≤ b),
        (ArithmeticFunction.moebius d : ℂ) *
          quadraticGaussDivisorBilinear (2 * N) (2 * N) d
            (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b‖ ≤
      3 * ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) / N := by
  exact (quadratic_low_correction_weight
    (fun d b => quadraticGaussDivisorBilinear (2 * N) (2 * N) d
      (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b) D B V).trans
    (quadratic_sqrt_normalized_gauss_bound (2 * B) N D hN v w hv hw
      K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hcost)

theorem quadratic_high_correction_band_bound (B N D : ℕ) (hB : 0 < B) (hD : 0 < D) (V : ℝ)
    (v w : ℕ → ℂ)
    (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ j) (K₂ j))
    (hcost : ∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) v) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) w) ≤ T) :
    ‖∑ d ∈ (Finset.Ioc D (2 * D)).filter
        (fun d : ℕ => V < (d : ℝ) ∧ (d : ℝ) ≤ ((2 * N) ^ 2 : ℕ)),
      ∑ b ∈ (oddSquarefreeRange (2 * B)).filter (fun b => B ≤ b),
        (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
          quadraticGaussDivisorBilinear (2 * N) (2 * N) d v w b‖ ≤
      3 * ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) /
        ((D : ℝ) * Real.sqrt B) := by
  apply (quadratic_correction_band_weight
    (fun d b => quadraticGaussDivisorBilinear (2 * N) (2 * N) d v w b)
      hD hB V ((2 * N) ^ 2 : ℕ)).trans
  have hh := quadratic_gauss_uniform_bound (2 * B) (2 * N) (2 * N) D v w
    K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hcost
  calc
    _ ≤ (1 / ((D : ℝ) * Real.sqrt B)) *
        (3 * (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) * (Nat.log 2 (2 * N) + 1) * T)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by push_cast; ring

end Ostmann

end OAI
