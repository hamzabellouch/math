import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMiddleBandGrowth

namespace OAI

/-! # Both original small-kernel corrections from the same shorter matrices -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticSmallHighBand (E B N D : ℕ) (P : ℕ → ℕ → Prop)
    (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
    if B ≤ b ∧ P d b then
      (((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
        quadraticDivisorBilinear (2 * N) (2 * N) d v w b else 0

noncomputable def quadraticSmallMiddleBand (ρ : 𝓢(ℝ, ℂ)) (M : ℝ) (E B N D L : ℕ)
    (P : ℕ → ℕ → Prop) (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
    if B ≤ b ∧ P d b then
      ((((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
        quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ))
          (quadraticSmallScale M b / (E * d : ℕ)) L) *
        quadraticDivisorBilinear (2 * N) (2 * N) d v w b else 0

noncomputable def quadraticSmallCorrectionGrowthScale (C ε ξ M A : ℝ) (B N : ℕ)
    (v w : ℕ → ℂ) : ℝ :=
  (C * (((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε) *
    (Real.sqrt M / Real.sqrt B * ((2 * B : ℕ) : ℝ) ^ ξ + A * (2 * N)) *
      (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
        Real.sqrt (quadraticDivisorMoment (2 * N) w))

private theorem matrix_bound {C ε ξ : ℝ} (hC : 0 ≤ C) {B N D : ℕ} (hD : 0 < D)
    (v w : ℕ → ℂ)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      ‖quadraticDivisorBilinear (2 * N) (2 * N) d v w b‖) ≤
      ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
        quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) D v w := by
  have hh := quadratic_bilinear_uniform_bound (2 * B) (2 * N) (2 * N) D v w
    (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N))
    (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N))
    (quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) D v w)
    (quadratic_growth_divisor_budget_nonneg hC _ _ _ _ _)
    (fun i _ => quadratic_growth_cutoff_nonneg hC _ _ i)
    (fun i _ => quadratic_growth_cutoff_nonneg hC _ _ i) hmat hmat
    (fun _ _ _ _ _ hp => quadratic_growth_cutoff_cost hC hD v w hp)
  simpa only [pow_two, Nat.cast_add, Nat.cast_one] using hh

private theorem weighted_budget {C ε ξ M A : ℝ} (hC : 0 ≤ C)
    {B N D : ℕ} (hM : 0 < M) (hB : 0 < B) (hD : 0 < D) (hA : 0 ≤ A)
    (hcut : Real.sqrt M / (Real.sqrt B * D) ≤ A) (v w : ℕ → ℂ) :
    (Real.sqrt M / (Real.sqrt B * D)) *
        quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) D v w ≤
      16 * quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w := by
  have hh := quadratic_second_growth_band_balance hM (show (0 : ℝ) ≤ (2 * N : ℕ) by positivity)
    (show (0 : ℝ) < B by exact_mod_cast hB) (show (1 : ℝ) ≤ D by exact_mod_cast hD)
    (show 0 ≤ C * (((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε by positivity)
    (show 0 ≤ ((2 * B : ℕ) : ℝ) ^ ξ by positivity)
    (show 0 ≤ Real.sqrt (quadraticDivisorMoment (2 * N) v) *
      Real.sqrt (quadraticDivisorMoment (2 * N) w) by positivity) hA hcut
  simpa only [quadraticGrowthDivisorBudget, quadraticSmallCorrectionGrowthScale,
    Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hh

theorem quadratic_small_high_growth {C ε ξ M A : ℝ} (hC : 0 ≤ C)
    {E B N D : ℕ} (hE : 1 ≤ E) (hM : 0 < M) (hB : 0 < B) (hD : 0 < D) (hA : 0 ≤ A)
    (hcut : Real.sqrt M / (Real.sqrt B * D) ≤ A)
    (P : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖(Real.sqrt M : ℂ) * quadraticSmallHighBand E B N D P v w‖ ≤
      16 * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
        quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w := by
  classical
  have hl := quadratic_variable_small_high_band E B N D hE hB hD P v w _
    (matrix_bound hC hD v w hmat)
  change ‖quadraticSmallHighBand E B N D P v w‖ ≤ _ at hl
  have hb := weighted_budget (ε := ε) (ξ := ξ) (N := N) hC hM hB hD hA hcut v w
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg M)]
  apply (mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg M)).trans
  calc
    _ = ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
        ((Real.sqrt M / (Real.sqrt B * D)) * quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) D v w) := by ring
    _ ≤ ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
        (16 * quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by ring

theorem quadratic_small_middle_growth (ρ : 𝓢(ℝ, ℂ))
    {C ε ξ M A : ℝ} (hC : 0 ≤ C)
    {E B N D L : ℕ} (hE : 1 ≤ E) (hM : 0 < M) (hB : 0 < B) (hD : 0 < D) (hA : 0 ≤ A)
    (hcut : Real.sqrt M / (Real.sqrt B * D) ≤ A)
    (P : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖(Real.sqrt M : ℂ) * quadraticSmallMiddleBand ρ M E B N D L P v w‖ ≤
      16 * (2 * L + 1) * quadraticSmallFourierBound ρ *
        ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w := by
  classical
  have hl := quadratic_variable_small_middle_band ρ M E B N D L hE hB hD P v w _
    (matrix_bound hC hD v w hmat)
  change ‖quadraticSmallMiddleBand ρ M E B N D L P v w‖ ≤ _ at hl
  have hb := weighted_budget (ε := ε) (ξ := ξ) (N := N) hC hM hB hD hA hcut v w
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg M)]
  apply (mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg M)).trans
  calc
    _ = ((2 * L + 1) * quadraticSmallFourierBound ρ * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2) *
        ((Real.sqrt M / (Real.sqrt B * D)) * quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) D v w) := by ring
    _ ≤ ((2 * L + 1) * quadraticSmallFourierBound ρ * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2) *
        (16 * quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w) :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg (mul_nonneg (by positivity)
        (quadraticSmallFourierBound_nonneg ρ)) (sq_nonneg _))
    _ = _ := by ring

end Ostmann

end OAI
