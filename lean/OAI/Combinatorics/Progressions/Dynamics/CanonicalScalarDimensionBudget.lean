import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace OAI

section

namespace Erdos3

theorem canonicalScalarDimensionBudget (d n : ℕ) {p : ℝ}
    (hn : (n : ℝ) ≤ p) :
    4 * (((d * n : ℕ) : ℝ) + 1) ≤ 8 * ((d : ℝ) + 1) * (p + 1) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hp : 0 ≤ p := (Nat.cast_nonneg n).trans hn
  have hdn := mul_le_mul_of_nonneg_left hn hd
  have hdp := mul_nonneg hd hp
  rw [Nat.cast_mul]
  nlinarith

theorem canonicalScalarDimensionBudget_fin_product (d : ℕ) {I : Type*} [Fintype I]
    {p : ℝ} (hn : (Fintype.card I : ℝ) ≤ p) :
    4 * ((Fintype.card (Fin d × I) : ℝ) + 1) ≤ 8 * ((d : ℝ) + 1) * (p + 1) := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    canonicalScalarDimensionBudget d (Fintype.card I) hn

end Erdos3

end

end OAI
