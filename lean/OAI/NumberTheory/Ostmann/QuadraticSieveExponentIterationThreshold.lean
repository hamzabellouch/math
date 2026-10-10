import OAI.NumberTheory.Ostmann.QuadraticSieveExponentIterationBasic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

theorem recursion_threshold_exponent {ξ : ℝ} (hξ : 1 ≤ ξ) :
    (2*ξ-1)/ξ = 2-1/ξ := by
  have hξ0 : ξ ≠ 0 := by linarith
  field_simp

theorem recursion_threshold_identity {N ξ : ℝ} (hN : 0 < N) (hξ : 1 ≤ ξ) :
    (N^((2*ξ-1)/ξ))^(1-ξ) * N^(2*ξ-1) = N^((2*ξ-1)/ξ) := by
  have hξ0 : ξ ≠ 0 := by linarith
  rw [← Real.rpow_mul hN.le, ← Real.rpow_add hN]
  congr 1
  field_simp
  ring

theorem recursion_threshold_bound {M N ξ : ℝ} (hN : 1 ≤ N) (hξ : 1 ≤ ξ)
    (hM : N^((2*ξ-1)/ξ) ≤ M) :
    M^(1-ξ) * N^(2*ξ-1) ≤ N^((2*ξ-1)/ξ) := by
  have hNp : 0 < N := by linarith
  have hpow := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos hNp ((2*ξ-1)/ξ)) hM (by linarith : 1-ξ ≤ 0)
  calc
    M^(1-ξ) * N^(2*ξ-1) ≤ (N^((2*ξ-1)/ξ))^(1-ξ) * N^(2*ξ-1) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hNp.le _)
    _ = _ := recursion_threshold_identity hNp hξ

theorem recursion_threshold_between {N ξ : ℝ} (hN : 1 ≤ N) (hξ : 1 ≤ ξ) :
    N ≤ N^((2*ξ-1)/ξ) ∧ N^((2*ξ-1)/ξ) ≤ N^2 := by
  have hξp : 0 < ξ := by linarith
  have he1 : 1 ≤ (2*ξ-1)/ξ := (le_div_iff₀ hξp).mpr (by linarith)
  have he2 : (2*ξ-1)/ξ ≤ 2 := (div_le_iff₀ hξp).mpr (by linarith)
  constructor
  · simpa using Real.rpow_le_rpow_of_exponent_le hN he1
  · simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hN he2

end Ostmann.QuadraticSieve

end

end OAI
