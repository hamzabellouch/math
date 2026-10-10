import OAI.NumberTheory.Ostmann.Quadratic.QuadraticUnitMiddleGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallCorrectionGrowth

namespace OAI

/-! # Small-kernel corrections at the unit divisor, including its full window -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_small_unit_weighted_growth {C ε ξ M A W : ℝ} (hC : 0 ≤ C)
    {B N : ℕ} (hM : 0 < M) (hB : 0 < B) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hcut : Real.sqrt M / Real.sqrt B ≤ A)
    (P : ℕ → Prop) (c : ℕ → ℂ) (v w : ℕ → ℂ)
    (hc : ∀ b ∈ oddSquarefreeRange (2 * B), B ≤ b → P b → ‖c b‖ ≤ W / Real.sqrt B)
    (hmat : QuadraticSieveBound (2 * B) (2 * N)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0)) :
    ‖(Real.sqrt M : ℂ) * (∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P b then
        c b * quadraticDivisorBilinear (2 * N) (2 * N) 1 v w b else 0)‖ ≤
      16 * W * quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w := by
  classical
  let T := quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) 1 v w
  let K := quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0
  have hK : 0 ≤ K := quadratic_growth_cutoff_nonneg hC _ _ _
  have hroot := quadratic_growth_unit_cost (ε := ε) (ξ := ξ) hC (2 * B) (2 * N) v w
  have hu := (quadratic_unit_divisor_bound (2 * B) (2 * N) (2 * N)
    K K hK hK hmat hmat v w).trans hroot
  have hf := quadratic_filtered_unit_bound B P c
    (fun b => quadraticDivisorBilinear (2 * N) (2 * N) 1 v w b)
    (A := W / Real.sqrt B) (by positivity) hc
  have hl := hf.trans (mul_le_mul_of_nonneg_left hu (show 0 ≤ W / Real.sqrt (B : ℝ) by positivity))
  have hb := quadratic_second_growth_band_balance hM (show (0 : ℝ) ≤ (2 * N : ℕ) by positivity)
    (show (0 : ℝ) < B by exact_mod_cast hB) (by norm_num : (1 : ℝ) ≤ 1)
    (show 0 ≤ C * (((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε by positivity)
    (show 0 ≤ ((2 * B : ℕ) : ℝ) ^ ξ by positivity)
    (show 0 ≤ Real.sqrt (quadraticDivisorMoment (2 * N) v) *
      Real.sqrt (quadraticDivisorMoment (2 * N) w) by positivity) hA (by simpa using hcut)
  have hb' : (Real.sqrt M / Real.sqrt B) * T ≤
      16 * quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w := by
    simpa only [T, quadraticGrowthDivisorBudget, quadraticSmallCorrectionGrowthScale,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_one, mul_assoc] using hb
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg M)]
  apply (mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg M)).trans
  calc
    _ = W * (Real.sqrt M / Real.sqrt B * T) := by ring
    _ ≤ W * (16 * quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w) :=
      mul_le_mul_of_nonneg_left hb' hW
    _ = _ := by ring

theorem quadratic_small_high_unit_growth {C ε ξ M A : ℝ} (hC : 0 ≤ C)
    {E B N : ℕ} (hE : 1 ≤ E) (hM : 0 < M) (hB : 0 < B) (hA : 0 ≤ A)
    (hcut : Real.sqrt M / Real.sqrt B ≤ A)
    (P : ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : QuadraticSieveBound (2 * B) (2 * N)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0)) :
    ‖(Real.sqrt M : ℂ) * (∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P b then
        (((ArithmeticFunction.moebius E : ℂ) / E) / (Real.sqrt b : ℂ)) *
          quadraticDivisorBilinear (2 * N) (2 * N) 1 v w b else 0)‖ ≤
      16 * quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w := by
  simpa only [mul_one] using quadratic_small_unit_weighted_growth hC hM hB hA
    (by norm_num : (0 : ℝ) ≤ 1) hcut P _ v w
    (fun b _ hb _ => by simpa only [Nat.cast_one, one_mul] using
      quadratic_moebius_root_weight (show 0 < (1 : ℕ) by decide) hB hE hb) hmat

theorem quadratic_small_middle_unit_growth (ρ : 𝓢(ℝ, ℂ))
    {C ε ξ M A : ℝ} (hC : 0 ≤ C)
    {E B N L : ℕ} (hE : 1 ≤ E) (hM : 0 < M) (hB : 0 < B) (hA : 0 ≤ A)
    (hcut : Real.sqrt M / Real.sqrt B ≤ A)
    (P : ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : QuadraticSieveBound (2 * B) (2 * N)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0)) :
    ‖(Real.sqrt M : ℂ) * (∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P b then
        ((((ArithmeticFunction.moebius E : ℂ) / E) / (Real.sqrt b : ℂ)) *
          quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ)) (quadraticSmallScale M b / E) L) *
          quadraticDivisorBilinear (2 * N) (2 * N) 1 v w b else 0)‖ ≤
      16 * (2 * L + 1) * quadraticSmallFourierBound ρ *
        quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w := by
  have hW : 0 ≤ (2 * L + 1 : ℝ) * quadraticSmallFourierBound ρ :=
    mul_nonneg (by positivity) (quadraticSmallFourierBound_nonneg ρ)
  let c : ℕ → ℂ := fun b =>
    (((ArithmeticFunction.moebius E : ℂ) / E) / (Real.sqrt b : ℂ)) *
      quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ)) (quadraticSmallScale M b / E) L
  have hc : ∀ b ∈ oddSquarefreeRange (2 * B), B ≤ b → P b →
      ‖c b‖ ≤ ((2 * L + 1) * quadraticSmallFourierBound ρ) / Real.sqrt B := by
    intro b _ hb _
    simpa only [c, mul_one, Nat.cast_one, one_mul] using
      quadratic_small_kernel_fourier_weight ρ (quadraticSmallScale M b / E) L
        (E := E) (D := 1) (d := 1) hE (by decide) hB le_rfl hb
  have hh := quadratic_small_unit_weighted_growth hC hM hB hA hW hcut P c v w hc hmat
  convert hh using 1
  ring

end Ostmann

end OAI
