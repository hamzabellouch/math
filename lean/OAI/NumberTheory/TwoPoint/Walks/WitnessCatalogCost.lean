import OAI.NumberTheory.TwoPoint.Bounds.EncodedWitnessSum
import OAI.NumberTheory.TwoPoint.Bounds.CrudeNumericalWordSum
import OAI.NumberTheory.TwoPoint.Walks.WitnessCodeBounds

namespace OAI

/-! Complete finite equality-pattern and witness-metadata cost. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def witnessCatalogCost (R T n M : ℕ) (VP VQ : ℝ) : ℝ :=
  ∑ t : Fin (T + 1), ∑ c : CrudeWordCode R t.val R,
    (Fintype.card (WitnessSystemData n M c.tupleClasses) : ℝ) *
      VP ^ Fintype.card c.tupleClasses *
      VQ ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses}

lemma witnessCatalogCost_nonneg (R T n M : ℕ) (VP VQ : ℝ)
    (hP : 0 ≤ VP) (hQ : 0 ≤ VQ) : 0 ≤ witnessCatalogCost R T n M VP VQ := by
  unfold witnessCatalogCost
  positivity

theorem witnessCatalogCost_exp_bound (R T n M : ℕ) (L C : ℝ)
    (hR : 1 ≤ R) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hslots : (T : ℝ) ≤ C * R * Real.log L)
    (hT : (T : ℝ) + 1 ≤ L ^ (2 : ℕ)) (hRp : (R : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hTM : T ≤ M + 1) (hnM : n ≤ M + 1) (hn : (n : ℝ) ≤ 4 * L)
    (hM : (M : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (VP VQ : ℝ) (hP : 0 ≤ VP) (hQ : 0 ≤ VQ)
    (hPup : VP ≤ L ^ (2 : ℕ)) (hQup : VQ ≤ L ^ (2 : ℕ)) :
    witnessCatalogCost R T n M VP VQ ≤
      Real.exp (63 * L * (Real.log L) ^ 2 + (3 + 7 * C) * R * (Real.log L) ^ 2) := by
  have hU : 1 ≤ L ^ (2 : ℕ) := one_le_pow₀ hL
  have hmeta (t : Fin (T + 1)) (c : CrudeWordCode R t.val R) :
      (Fintype.card (WitnessSystemData n M c.tupleClasses) : ℝ) ≤
        Real.exp (63 * L * (Real.log L) ^ 2) := by
    apply card_witnessSystemData_scale n M c.tupleClasses L hL hlog _ hnM hn hM
    have hc := c.class_count_le_slots
    omega
  calc
    _ ≤ ∑ t : Fin (T + 1), ∑ c : CrudeWordCode R t.val R,
        Real.exp (63 * L * (Real.log L) ^ 2) * (L ^ (2 : ℕ)) ^ T := by
      apply sum_le_sum
      intro t _
      apply sum_le_sum
      intro c _
      have hmass := (c.class_mass_le hP hQ hPup hQup hU).trans
        (pow_le_pow_right₀ hU (show t.val ≤ T by omega))
      calc
        _ = (Fintype.card (WitnessSystemData n M c.tupleClasses) : ℝ) *
            (VP ^ Fintype.card c.tupleClasses *
              VQ ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses}) := by ring
        _ ≤ _ := mul_le_mul (hmeta t c) hmass (by positivity) (by positivity)
    _ = Real.exp (63 * L * (Real.log L) ^ 2) *
        ((∑ t : Fin (T + 1), (Fintype.card (CrudeWordCode R t.val R) : ℝ)) *
          (L ^ (2 : ℕ)) ^ T) := by
      simp only [sum_const, card_univ, nsmul_eq_mul]
      rw [sum_mul, mul_sum]
      apply sum_congr rfl
      intro t _
      ring
    _ ≤ Real.exp (63 * L * (Real.log L) ^ 2) *
        Real.exp ((3 + 7 * C) * R * (Real.log L) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      convert crude_numerical_cost_exp_bound R T 2 L C (L ^ (2 : ℕ)) hR
        (zero_lt_one.trans_le hL) hlog hslots hT hRp hU le_rfl using 1
      congr 1
      ring
    _ = _ := (Real.exp_add _ _).symm

end TwoPointCorrelations

end OAI
