import OAI.NumberTheory.Ostmann.Arithmetic.BulkHalfLogBudgetComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternKernelCost

namespace OAI

/-! # Fixed-depth cost of the terminal logarithmic cutoffs -/

namespace Ostmann
open scoped SchwartzMap

/-- Retaining all terminal log weights preserves the quadratic budget,
uniformly in their centers and in the moving Fourier window. -/
theorem movingPatternHalfLogKernelBudget_spectatorScale_window
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (A H B D Dlog : ℝ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hDlog : 0 ≤ Dlog) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      let m := spectatorBulkCount k L
      ∀ lo hi : ℝ, lo ≤ hi → hi - lo ≤ Real.exp (H * m) →
      ∀ t rlog : ℕ, t ≤ 4 * 2 ^ n → rlog ≤ 2 ^ n * (r₀ + m + 4 * n) →
      bulkLogWeightedKernelPairBudget ψ (Real.exp (A * m)) lo hi n
        (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 t rlog B D Dlog ≤
      Real.exp (C * L ^ 2) := by
  obtain ⟨C₀, hC₀, hb⟩ :=
    movingPatternKernelBudget_spectatorScale_window ψ n r₀ k A H B D hA hH
  let a := 2 + Dlog * (Real.exp 2 - 1)
  let K := 2 * a ^ (4 * 2 ^ n)
  have ha : 1 ≤ a := by
    have he : 0 ≤ Real.exp 2 - 1 := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
    dsimp only [a]
    nlinarith [mul_nonneg hDlog he]
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨C₀ + K, by linarith, ?_⟩
  intro L hL
  dsimp only
  intro lo hi hhi hwindow t rlog ht hrlog
  have hbudget := bulkHalfLogWeightedKernelPairBudget_le ψ (Real.exp (A * spectatorBulkCount k L))
    lo hi n (2 ^ n * (r₀ + spectatorBulkCount k L + 4 * n + 4))
    (2 ^ n * (r₀ + spectatorBulkCount k L + 4 * n)) 0 t rlog B D Dlog hDlog ht hrlog
  have hfactor : 2 * a ^ t ≤ K :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha ht) (by norm_num)
  have hbase := bulkKernelPairComparisonBudget_nonneg ψ
    (Real.exp (A * spectatorBulkCount k L)) lo hi n
    (2 ^ n * (r₀ + spectatorBulkCount k L + 4 * n + 4))
    (2 ^ n * (r₀ + spectatorBulkCount k L + 4 * n)) 0 B D
  apply hbudget.trans
  calc
    _ ≤ K * Real.exp (C₀ * L ^ 2) := mul_le_mul hfactor (hb L hL lo hi hhi hwindow) hbase hK
    _ ≤ Real.exp K * Real.exp (C₀ * L ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp K]) (Real.exp_nonneg _)
    _ = Real.exp (K + C₀ * L ^ 2) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((C₀ + K) * L ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hsq : 1 ≤ L ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq hK]

end Ostmann

end OAI
