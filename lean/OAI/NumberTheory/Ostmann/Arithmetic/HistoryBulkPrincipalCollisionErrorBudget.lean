import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceCollisionBudget

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError
open Construction Conclusion Filter HistoryBulkSourceCollision

theorem selected_compensated_collision_budget_eventually (k : ℕ) (A D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k, ∀ outside : List ℕ,
      (∀ p ∈ outside, 0 < p) → outside.length ≤ bulkSize k L →
      (∀ p ∈ outside, Real.log (p : ℝ) ≤ Real.exp ((1/1000 : ℝ)*L)) →
      ((outside.prod : ℝ)^(2^(l+1)) * Real.exp (A*((bulkSize k L : ℝ)+1))) *
        Real.exp (D*(L+1)^2) * ((2^l*(2*(bulkSize k L/2)) : ℕ) : ℝ)^2 *
        Real.exp (L-Real.exp ((39/10000 : ℝ)*L)) *
        Real.exp (2*(2 : ℝ)^l*(bulkSize k L : ℝ)) ≤
      Real.exp (-Real.exp ((1/500 : ℝ)*L)) := by
  filter_upwards [selected_collision_budget_eventually k (A+2*(2 : ℝ)^k) D] with L hL
  intro l hl outside hpos hlen hlog
  have hpow : (2 : ℝ)^l ≤ (2 : ℝ)^k := pow_le_pow_right₀ (by norm_num) hl
  have hkernel :
      Real.exp (A*((bulkSize k L : ℝ)+1)) *
        Real.exp (2*(2 : ℝ)^l*(bulkSize k L : ℝ)) ≤
      Real.exp ((A+2*(2 : ℝ)^k)*((bulkSize k L : ℝ)+1)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hm := Nat.cast_nonneg (bulkSize k L) (α := ℝ)
    have hmul := mul_le_mul_of_nonneg_right hpow hm
    have hp : 0 ≤ (2 : ℝ)^k := pow_nonneg (by norm_num) k
    nlinarith
  calc
    _ = (outside.prod : ℝ)^(2^(l+1)) *
        (Real.exp (A*((bulkSize k L : ℝ)+1)) *
          Real.exp (2*(2 : ℝ)^l*(bulkSize k L : ℝ))) *
        Real.exp (D*(L+1)^2) * ((2^l*(2*(bulkSize k L/2)) : ℕ) : ℝ)^2 *
        Real.exp (L-Real.exp ((39/10000 : ℝ)*L)) := by ring
    _ ≤ ((outside.prod : ℝ)^(2^(l+1)) *
        Real.exp ((A+2*(2 : ℝ)^k)*((bulkSize k L : ℝ)+1))) *
        Real.exp (D*(L+1)^2) * ((2^l*(2*(bulkSize k L/2)) : ℕ) : ℝ)^2 *
        Real.exp (L-Real.exp ((39/10000 : ℝ)*L)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul_of_nonneg_left hkernel (by positivity)
    _ ≤ _ := hL l hl outside hpos hlen hlog

end Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError

end

end OAI
