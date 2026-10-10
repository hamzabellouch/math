import OAI.NumberTheory.Ostmann.Quadratic.QuadraticUnitMiddle
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticVariableCorrectionCutoff

namespace OAI

/-! # Filtered boundary corrections retain the full frequency comparison -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_unit_sqrt_gauss_bound (M N : ℕ) (hN : 0 < N)
    (v w : ℕ → ℂ) (hv : ∀ n < N, v n = 0) (hw : ∀ n < N, w n = 0)
    (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M (2 * N) K₁) (h₂ : QuadraticSieveBound M (2 * N) K₂) :
    (∑ m ∈ oddSquarefreeRange M,
      ‖quadraticGaussDivisorBilinear (2 * N) (2 * N) 1
        (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) m‖) ≤
      3 * (Real.sqrt (2 * K₁ * quadraticDivisorMoment (2 * N) v) *
        Real.sqrt (2 * K₂ * quadraticDivisorMoment (2 * N) w)) / N := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hroot : Real.sqrt (2 * K₁ * quadraticDivisorMoment (2 * N) (quadraticSqrtNormalize v)) *
      Real.sqrt (2 * K₂ * quadraticDivisorMoment (2 * N) (quadraticSqrtNormalize w)) ≤
      (Real.sqrt (2 * K₁ * quadraticDivisorMoment (2 * N) v) *
        Real.sqrt (2 * K₂ * quadraticDivisorMoment (2 * N) w)) / N := by
    calc
      _ ≤ Real.sqrt (2 * K₁ * (quadraticDivisorMoment (2 * N) v / N)) *
          Real.sqrt (2 * K₂ * (quadraticDivisorMoment (2 * N) w / N)) := by
        apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
            (quadraticSqrtNormalize_moment N (2 * N) hN v hv) (by positivity))
        · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
            (quadraticSqrtNormalize_moment N (2 * N) hN w hw) (by positivity))
      _ = _ := by
        rw [← mul_div_assoc, ← mul_div_assoc, Real.sqrt_div' _ hNr.le, Real.sqrt_div' _ hNr.le,
          div_mul_div_comm, ← pow_two, Real.sq_sqrt hNr.le]
  exact (quadratic_gauss_unit_divisor_bound M (2 * N) (2 * N) K₁ K₂ hK₁ hK₂ h₁ h₂ _ _).trans
    (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 3))

theorem quadratic_filtered_unit_bound (B : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (c F : ℕ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hc : ∀ b ∈ oddSquarefreeRange (2 * B), B ≤ b → P b → ‖c b‖ ≤ A) :
    ‖∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P b then c b * F b else 0‖ ≤
      A * ∑ b ∈ oddSquarefreeRange (2 * B), ‖F b‖ := by
  calc
    _ ≤ ∑ b ∈ oddSquarefreeRange (2 * B), A * ‖F b‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b hb
      split_ifs with h
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hc b hb h.1 h.2) (norm_nonneg _)
      · rw [norm_zero]
        exact mul_nonneg hA (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

theorem quadratic_filtered_unit_root_weight (B d : ℕ) (hB : 0 < B) (hd : 0 < d)
    (P : ℕ → Prop) [DecidablePred P] (F : ℕ → ℂ) :
    ‖∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P b then
        (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) * F b else 0‖ ≤
      (1 / ((d : ℝ) * Real.sqrt B)) * ∑ b ∈ oddSquarefreeRange (2 * B), ‖F b‖ := by
  apply quadratic_filtered_unit_bound B P _ F (by positivity)
  intro b _ hb _
  exact quadratic_moebius_root_weight hd hB le_rfl hb

end Ostmann

end OAI
