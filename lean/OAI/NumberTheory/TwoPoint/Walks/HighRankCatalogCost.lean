import OAI.NumberTheory.TwoPoint.Walks.HighRankPaddingSum

namespace OAI

/-! Explicit cost of every column pattern and every squarefree padding word. -/

namespace TwoPointCorrelations

open Finset

theorem column_padding_catalog_cost_exp_bound (J R M : ℕ) (L Cj Cm U : ℝ)
    (hR : 1 ≤ R) (hL : 0 < L) (hlog : 1 ≤ Real.log L)
    (hJ : (J : ℝ) ≤ Cj * Real.log L) (hM : (M : ℝ) ≤ Cm * Real.log L)
    (hT : ((R * M : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hRpoly : (R : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hU : 1 ≤ U) (hUP : U ≤ L ^ (2 : ℕ)) :
    ((Fintype.card (CrudeColumnPatternCode J R) : ℝ) * U ^ (R * J)) *
      ((∑ n : Fin (R * M + 1), (Fintype.card (CrudeWordCode R n.val R) : ℝ)) *
        U ^ (R * M)) ≤
      Real.exp ((3 + 7 * Cm + 4 * Cj) * R * (Real.log L) ^ 2) := by
  have hc := crude_column_pattern_count_bound J R L Cj hL hJ hRpoly
  have hp : U ^ (R * J) ≤ Real.exp (2 * Cj * R * (Real.log L) ^ 2) := by
    calc
      _ ≤ (L ^ (2 : ℕ)) ^ (R * J) := pow_le_pow_left₀ (by linarith) hUP _
      _ = Real.exp (((R * J : ℕ) : ℝ) * (2 * Real.log L)) := by
        rw [Real.exp_nat_mul]
        congr 1
        rw [show 2 * Real.log L = Real.log L + Real.log L by ring,
          Real.exp_add, Real.exp_log hL]
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_left hJ
          (show 0 ≤ 2 * R * Real.log L by positivity)
        push_cast
        nlinarith
  have hslots : ((R * M : ℕ) : ℝ) ≤ Cm * R * Real.log L := by
    have hm := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg R : (0 : ℝ) ≤ R)
    push_cast
    nlinarith
  have hpad := crude_numerical_cost_exp_bound R (R * M) 2 L Cm U hR hL hlog
    hslots hT hRpoly hU hUP
  calc
    _ ≤ (Real.exp (2 * Cj * R * (Real.log L) ^ 2) *
        Real.exp (2 * Cj * R * (Real.log L) ^ 2)) *
        Real.exp ((3 + 5 * Cm + 2 * Cm) * R * (Real.log L) ^ 2) := by
      exact mul_le_mul (mul_le_mul hc hp (by positivity) (Real.exp_pos _).le)
        hpad (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end TwoPointCorrelations

end OAI
