import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDoubledBandBudget
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGrowthDivisorBudget
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticVariableMatrixBands

namespace OAI

/-! # Original low and high correction bands from the actual growth matrices -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticLowCorrectionBand (B N D : ℕ) (P : ℕ → ℕ → Prop)
    (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
    if B ≤ b ∧ P d b then (ArithmeticFunction.moebius d : ℂ) *
      quadraticGaussDivisorBilinear (2 * N) (2 * N) d
        (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b else 0

noncomputable def quadraticHighCorrectionBand (B N D : ℕ) (P : ℕ → ℕ → Prop)
    (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
    if B ≤ b ∧ P d b then
      (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
        quadraticGaussDivisorBilinear (2 * N) (2 * N) d v w b else 0

noncomputable def quadraticCorrectionGrowthScale (C ε ξ M : ℝ) (e B N : ℕ)
    (v w : ℕ → ℂ) : ℝ :=
  (C * (((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε) *
    (2 * (M / e) + Real.sqrt (2 * (M / e)) / Real.sqrt B * ((2 * B : ℕ) : ℝ) ^ ξ) *
      (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
        Real.sqrt (quadraticDivisorMoment (2 * N) w))

theorem quadratic_low_band_growth {C ε ξ M J : ℝ} (hC : 0 ≤ C)
    {e B N D : ℕ} (hM : 0 < M) (he : 0 < e) (hB : 0 < B) (hN : 0 < N) (hD : 0 < D)
    (hJ : 1 ≤ J) (hcut : (D : ℝ) ≤ 2 * quadraticCorrectionBase M N e B * J)
    (P : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hv : ∀ n < N, v n = 0) (hw : ∀ n < N, w n = 0)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖((M / e : ℝ) : ℂ) * quadraticLowCorrectionBand B N D P v w‖ ≤
      96 * J * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
        quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
  classical
  let T := quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) D v w
  have hT : 0 ≤ T := quadratic_growth_divisor_budget_nonneg hC _ _ _ _ _
  have hl := quadratic_variable_low_band_bound B N D hN P v w hv hw
    (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N))
    (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N)) T hT
    (fun i _ => quadratic_growth_cutoff_nonneg hC _ _ i)
    (fun i _ => quadratic_growth_cutoff_nonneg hC _ _ i) hmat hmat
    (fun _ _ _ _ _ hp => quadratic_growth_cutoff_cost hC hD v w hp)
  change ‖quadraticLowCorrectionBand B N D P v w‖ ≤ _ at hl
  have hb := quadratic_first_low_budget hM (show (0 : ℝ) < N by exact_mod_cast hN)
    he hB hD hJ
    (show 0 ≤ C * (((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε by positivity)
    (show 0 ≤ ((2 * B : ℕ) : ℝ) ^ ξ by positivity)
    (show 0 ≤ Real.sqrt (quadraticDivisorMoment (2 * N) v) *
      Real.sqrt (quadraticDivisorMoment (2 * N) w) by positivity) hcut
  have hb' : (M / ((e : ℝ) * N)) * T ≤
      32 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
    simpa only [T, quadraticGrowthDivisorBudget, quadraticCorrectionGrowthScale,
      Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hb
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hM (by exact_mod_cast he))]
  apply (mul_le_mul_of_nonneg_left hl (by positivity)).trans
  calc
    _ = (3 * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2) * (M / ((e : ℝ) * N) * T) := by ring
    _ ≤ (3 * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2) *
        (32 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w) :=
      mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
