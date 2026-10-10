import OAI.NumberTheory.TwoPoint.Bounds.MatrixMomentNorm
import OAI.NumberTheory.TwoPoint.Bounds.SpectralTransfer

namespace OAI

/-! The exact unnormalized moment controls the exceptional block origins.
No self-adjointness of the nonbacktracking matrix is needed. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def realMatrixSpectralRadius {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) : ℝ :=
  (spectralRadius ℂ (matrixOperator (fun i j => (A i j : ℂ)))).toReal

lemma real_matrix_spectral_power_le {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (k : ℕ) (hk : 0 < k) :
    realMatrixSpectralRadius A ^ (2 * k) ≤ matrixFrobeniusSq (A ^ k) := by
  let T := matrixOperator (fun i j => (A i j : ℂ))
  have hp := (spectrum.spectralRadius_pow_le (𝕜 := ℂ) T k (by omega)).trans
    (spectralRadius_le_nnnorm (𝕜 := ℂ) (T ^ k))
  have hr : realMatrixSpectralRadius A ^ k ≤ ‖T ^ k‖ := by
    have ht := ENNReal.toReal_mono (by exact ENNReal.coe_ne_top) hp
    simpa only [realMatrixSpectralRadius, ENNReal.toReal_pow, ENNReal.coe_toReal,
      coe_nnnorm] using ht
  have hm := hr.trans (real_matrix_operator_power_norm_le A k)
  have hnonneg : 0 ≤ realMatrixSpectralRadius A ^ k := pow_nonneg ENNReal.toReal_nonneg _
  have hs := (sq_le_sq₀ hnonneg (Real.sqrt_nonneg _)).mpr hm
  rw [Real.sq_sqrt (matrixFrobeniusSq_nonneg _)] at hs
  simpa only [Nat.mul_comm 2 k, pow_mul] using hs

theorem FiniteLaw.matrix_spectral_tail {V Ω : Type*}
    [Fintype V] [DecidableEq V] [Fintype Ω]
    (μ : FiniteLaw Ω) (A : Ω → Matrix V V ℝ) (k : ℕ) (hk : 0 < k)
    (B : ℝ) (hB : 0 < B)
    (hmoment : μ.average (fun x => matrixFrobeniusSq (A x ^ k)) ≤ B ^ (2 * k)) :
    μ.probability (fun x => Real.exp 1 * B < realMatrixSpectralRadius (A x)) ≤
      Real.exp (-(2 * k : ℕ)) := by
  have hden : 0 < (Real.exp 1 * B) ^ (2 * k) := pow_pos (mul_pos (Real.exp_pos _) hB) _
  calc
    _ ≤ μ.average (fun x => matrixFrobeniusSq (A x ^ k) / (Real.exp 1 * B) ^ (2 * k)) := by
      apply μ.average_mono
      intro x
      by_cases hx : Real.exp 1 * B < realMatrixSpectralRadius (A x)
      · rw [ite_eq_left hx]
        apply (one_le_div hden).mpr
        exact (pow_le_pow_left₀ (by positivity) hx.le _).trans
          (real_matrix_spectral_power_le (A x) k hk)
      · rw [ite_eq_right hx]
        exact div_nonneg (matrixFrobeniusSq_nonneg _) hden.le
    _ = μ.average (fun x => matrixFrobeniusSq (A x ^ k)) / (Real.exp 1 * B) ^ (2 * k) := by
      simp only [div_eq_mul_inv, μ.average_mul_const]
    _ ≤ B ^ (2 * k) / (Real.exp 1 * B) ^ (2 * k) :=
      div_le_div_of_nonneg_right hmoment hden.le
    _ = ((Real.exp 1) ^ (2 * k))⁻¹ := by
      rw [mul_pow]
      field_simp
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1
      simp

lemma trace_moment_add_one_le (B : ℝ) (hB : 1 ≤ B) (n : ℕ) (hn : 0 < n) :
    B ^ n + 1 ≤ (2 * B) ^ n := by
  have hb : 1 ≤ B ^ n := one_le_pow₀ hB
  have ht : (2 : ℝ) ≤ 2 ^ n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [pow_succ]
    nlinarith [(one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2 ^ m)]
  rw [mul_pow]
  nlinarith

theorem FiniteLaw.matrix_spectral_tail_add_one {V Ω : Type*}
    [Fintype V] [DecidableEq V] [Fintype Ω]
    (μ : FiniteLaw Ω) (A : Ω → Matrix V V ℝ) (k : ℕ) (hk : 0 < k)
    (B : ℝ) (hB : 1 ≤ B)
    (hmoment : μ.average (fun x => matrixFrobeniusSq (A x ^ k)) ≤ B ^ (2 * k) + 1) :
    μ.probability (fun x => Real.exp 1 * (2 * B) < realMatrixSpectralRadius (A x)) ≤
      Real.exp (-(2 * k : ℕ)) := by
  exact μ.matrix_spectral_tail A k hk (2 * B) (by linarith)
    (hmoment.trans (trace_moment_add_one_le B hB (2 * k) (by omega)))

end TwoPointCorrelations

end OAI
