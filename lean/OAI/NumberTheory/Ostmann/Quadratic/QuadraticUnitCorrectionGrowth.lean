import OAI.NumberTheory.Ostmann.Quadratic.QuadraticUnitCorrectionBounds
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGrowthCorrectionBands

namespace OAI

/-! # The missing unit-divisor endpoint has the same normalized growth rate -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticLowCorrectionUnit (B N : ℕ) (P : ℕ → Prop)
    (v w : ℕ → ℂ) : ℂ :=
  ∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P b then
    quadraticGaussDivisorBilinear (2 * N) (2 * N) 1
      (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b else 0

noncomputable def quadraticHighCorrectionUnit (B N : ℕ) (P : ℕ → Prop)
    (v w : ℕ → ℂ) : ℂ :=
  ∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P b then
    (1 / (Real.sqrt b : ℂ)) * quadraticGaussDivisorBilinear (2 * N) (2 * N) 1 v w b else 0

theorem quadratic_growth_unit_cost {C ε ξ : ℝ} (hC : 0 ≤ C)
    (B N : ℕ) (v w : ℕ → ℂ) :
    Real.sqrt (2 * quadraticGrowthCutoff C ε ξ B N 0 * quadraticDivisorMoment N v) *
      Real.sqrt (2 * quadraticGrowthCutoff C ε ξ B N 0 * quadraticDivisorMoment N w) ≤
        quadraticGrowthDivisorBudget C ε ξ B N 1 v w := by
  simpa only [pow_zero, Nat.cast_one, mul_one] using
    quadratic_growth_cutoff_cost hC (show 0 < (1 : ℕ) by decide) v w
      (i := 0) (j := 0) (by norm_num)

theorem quadratic_low_unit_growth {C ε ξ M J : ℝ} (hC : 0 ≤ C)
    {e B N : ℕ} (hM : 0 < M) (he : 0 < e) (hB : 0 < B) (hN : 0 < N)
    (hJ : 1 ≤ J) (hcut : 1 ≤ 2 * quadraticCorrectionBase M N e B * J)
    (P : ℕ → Prop) (v w : ℕ → ℂ)
    (hv : ∀ n < N, v n = 0) (hw : ∀ n < N, w n = 0)
    (hmat : QuadraticSieveBound (2 * B) (2 * N)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0)) :
    ‖((M / e : ℝ) : ℂ) * quadraticLowCorrectionUnit B N P v w‖ ≤
      96 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
  classical
  let T := quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) 1 v w
  let K := quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0
  have hK : 0 ≤ K := quadratic_growth_cutoff_nonneg hC _ _ _
  have hroot := quadratic_growth_unit_cost (ε := ε) (ξ := ξ) hC (2 * B) (2 * N) v w
  have hl : ‖quadraticLowCorrectionUnit B N P v w‖ ≤ 3 * T / N := by
    have hf := quadratic_filtered_unit_bound B P (fun _ => 1)
      (fun b => quadraticGaussDivisorBilinear (2 * N) (2 * N) 1
        (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b)
      (A := 1) (by norm_num) (by intros; norm_num)
    have hu := quadratic_unit_sqrt_gauss_bound (2 * B) N hN v w hv hw K K hK hK hmat hmat
    apply (show ‖quadraticLowCorrectionUnit B N P v w‖ ≤ _ by simpa [quadraticLowCorrectionUnit] using hf).trans
    apply hu.trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 3)) (Nat.cast_nonneg N)
  have hb := quadratic_first_low_budget hM (show (0 : ℝ) < N by exact_mod_cast hN)
    he hB (show 0 < (1 : ℕ) by decide) hJ
    (show 0 ≤ C * (((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε by positivity)
    (show 0 ≤ ((2 * B : ℕ) : ℝ) ^ ξ by positivity)
    (show 0 ≤ Real.sqrt (quadraticDivisorMoment (2 * N) v) *
      Real.sqrt (quadraticDivisorMoment (2 * N) w) by positivity) (by simpa using hcut)
  have hb' : (M / ((e : ℝ) * N)) * T ≤
      32 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
    simpa only [T, quadraticGrowthDivisorBudget, quadraticCorrectionGrowthScale,
      Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hb
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hM (by exact_mod_cast he))]
  apply (mul_le_mul_of_nonneg_left hl (by positivity)).trans
  calc
    _ = 3 * (M / ((e : ℝ) * N) * T) := by ring
    _ ≤ 3 * (32 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w) :=
      mul_le_mul_of_nonneg_left hb' (by norm_num)
    _ = _ := by ring

theorem quadratic_high_unit_growth {C ε ξ M J : ℝ} (hC : 0 ≤ C)
    {e B N : ℕ} (hM : 0 < M) (he : 0 < e) (hB : 0 < B) (hN : 0 < N)
    (hJ : 1 ≤ J) (hcut : quadraticCorrectionBase M N e B / (8 * J) ≤ 1)
    (P : ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : QuadraticSieveBound (2 * B) (2 * N)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0)) :
    ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticHighCorrectionUnit B N P v w‖ ≤
      384 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
  classical
  let T := quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) 1 v w
  let K := quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0
  have hK : 0 ≤ K := quadratic_growth_cutoff_nonneg hC _ _ _
  have hroot := quadratic_growth_unit_cost (ε := ε) (ξ := ξ) hC (2 * B) (2 * N) v w
  have hl : ‖quadraticHighCorrectionUnit B N P v w‖ ≤ 3 * T / Real.sqrt B := by
    have hf := quadratic_filtered_unit_root_weight B 1 hB (by decide) P
      (fun b => quadraticGaussDivisorBilinear (2 * N) (2 * N) 1 v w b)
    have hu := (quadratic_gauss_unit_divisor_bound (2 * B) (2 * N) (2 * N)
      K K hK hK hmat hmat v w).trans
      (mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 3))
    have hf' : ‖quadraticHighCorrectionUnit B N P v w‖ ≤
        (1 / Real.sqrt B) * ∑ b ∈ oddSquarefreeRange (2 * B),
          ‖quadraticGaussDivisorBilinear (2 * N) (2 * N) 1 v w b‖ := by
      simpa [quadraticHighCorrectionUnit] using hf
    exact hf'.trans (by simpa [T, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hu (show 0 ≤ 1 / Real.sqrt (B : ℝ) by positivity))
  have hb := quadratic_first_high_budget hM (show (0 : ℝ) < N by exact_mod_cast hN)
    he hB (show 0 < (1 : ℕ) by decide) hJ
    (show 0 ≤ C * (((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε by positivity)
    (show 0 ≤ ((2 * B : ℕ) : ℝ) ^ ξ by positivity)
    (show 0 ≤ Real.sqrt (quadraticDivisorMoment (2 * N) v) *
      Real.sqrt (quadraticDivisorMoment (2 * N) w) by positivity) (by simpa using hcut)
  have hb' : (Real.sqrt M / (Real.sqrt e * Real.sqrt B)) * T ≤
      128 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w := by
    simpa only [T, quadraticGrowthDivisorBudget, quadraticCorrectionGrowthScale,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_one, mul_assoc] using hb
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left hl (by positivity)).trans
  calc
    _ = 3 * (Real.sqrt M / (Real.sqrt e * Real.sqrt B) * T) := by ring
    _ ≤ 3 * (128 * J * quadraticCorrectionGrowthScale C ε ξ M e B N v w) :=
      mul_le_mul_of_nonneg_left hb' (by norm_num)
    _ = _ := by ring

end Ostmann

end OAI
