import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGrowthCorrectionBands

namespace OAI

/-! # The actual high-divisor correction with its original normalizer -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_high_band_growth {C ε ξ M J : ℝ} (hC : 0 ≤ C)
    {e B N D : ℕ} (hM : 0 < M) (he : 0 < e) (hB : 0 < B) (hN : 0 < N) (hD : 0 < D)
    (hJ : 1 ≤ J) (hcut : quadraticCorrectionBase M N e B / (8 * J) ≤ (D : ℝ))
    (P : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticHighCorrectionBand B N D P v w‖ ≤
      384 * J * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
        quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
  classical
  let T := quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) D v w
  have hT : 0 ≤ T := quadratic_growth_divisor_budget_nonneg hC _ _ _ _ _
  have hl := quadratic_variable_high_band_bound B N D hB hD P v w
    (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N))
    (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N)) T hT
    (fun i _ => quadratic_growth_cutoff_nonneg hC _ _ i)
    (fun i _ => quadratic_growth_cutoff_nonneg hC _ _ i) hmat hmat
    (fun _ _ _ _ _ hp => quadratic_growth_cutoff_cost hC hD v w hp)
  change ‖quadraticHighCorrectionBand B N D P v w‖ ≤ _ at hl
  have hb := quadratic_first_high_budget hM (show (0 : ℝ) < N by exact_mod_cast hN)
    he hB hD hJ
    (show 0 ≤ C * (((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε by positivity)
    (show 0 ≤ ((2 * B : ℕ) : ℝ) ^ ξ by positivity)
    (show 0 ≤ Real.sqrt (quadraticDivisorMoment (2 * N) v) *
      Real.sqrt (quadraticDivisorMoment (2 * N) w) by positivity) hcut
  have hb' : (Real.sqrt M / (Real.sqrt e * Real.sqrt B * D)) * T ≤
      128 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
    simpa only [T, quadraticGrowthDivisorBudget, quadraticCorrectionGrowthScale,
      Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hb
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left hl (by positivity)).trans
  calc
    _ = (3 * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2) *
        (Real.sqrt M / (Real.sqrt e * Real.sqrt B * D) * T) := by ring
    _ ≤ (3 * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2) *
        (128 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w) :=
      mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
