import OAI.NumberTheory.Ostmann.Arithmetic.BulkLogWeightedKernelPairComparison

namespace OAI

/-! # Cost of retaining the original terminal logarithmic factors -/

namespace Ostmann
open scoped SchwartzMap

/-- Two half-bulk factors per leaf in each tree fit the existing derivative-root budget. -/
theorem bulkHalfLogWeightedKernelPairBudget_le
    (ψ : 𝓢(ℝ, ℂ)) (V lo hi : ℝ) (n d r e t rlog : ℕ) (B D Dlog : ℝ)
    (hDlog : 0 ≤ Dlog) (ht : t ≤ 4 * 2 ^ n) (hr : rlog ≤ r) :
    bulkLogWeightedKernelPairBudget ψ V lo hi n d r e t rlog B D Dlog ≤
      (2 * (2 + Dlog * (Real.exp 2 - 1)) ^ t) *
        bulkKernelPairComparisonBudget ψ V lo hi n d r e B D := by
  let H := 2 * (n * d + e) + r
  let A := (2 ^ n + (2 ^ n - 1)) * H
  let B' := (3 * (2 ^ n - 1) + 2 * 2 ^ n) * H
  have htr : t * rlog ≤ 2 * B' := by
    calc
      _ ≤ (4 * 2 ^ n) * r := Nat.mul_le_mul ht hr
      _ = 2 * ((2 * 2 ^ n) * r) := by ring
      _ ≤ 2 * B' := Nat.mul_le_mul_left 2
        (Nat.mul_le_mul (by omega)
          (show r ≤ H by dsimp only [H]; omega))
  have hcount : 2 * (A + B') + t * rlog + 1 ≤ 2 * (2 * (A + B') + 1) := by omega
  have hcountR : ((2 * (A + B') + t * rlog + 1 : ℕ) : ℝ) ≤
      2 * ((2 * (A + B') + 1 : ℕ) : ℝ) := by exact_mod_cast hcount
  have hexp : 0 ≤ Real.exp 2 - 1 := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  have hfactor : 0 ≤ (2 + Dlog * (Real.exp 2 - 1)) ^ t :=
    pow_nonneg (add_nonneg (by norm_num) (mul_nonneg hDlog hexp)) _
  have h := mul_le_mul_of_nonneg_right hcountR
    (mul_nonneg (sq_nonneg
      (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1))) hfactor)
  change ((2 * (A + B') + t * rlog + 1 : ℕ) : ℝ) *
      ((movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 *
        (2 + Dlog * (Real.exp 2 - 1)) ^ t) ≤ _
  exact h.trans_eq (by dsimp only [bulkKernelPairComparisonBudget, A, B', H]; ring)

end Ostmann

end OAI
