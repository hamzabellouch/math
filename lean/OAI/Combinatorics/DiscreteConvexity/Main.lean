import OAI.Combinatorics.DiscreteConvexity.HalfDensity
import OAI.Combinatorics.DiscreteConvexity.DensityConstants
import OAI.Combinatorics.DiscreteConvexity.LabelCoupling
import OAI.Combinatorics.DiscreteConvexity.MandatoryCoupling
import OAI.Combinatorics.DiscreteConvexity.UnionTuples

namespace OAI

/-!
# Talagrand discrete convexity at the original density

Independent coordinate choices produce dependent rows with full Bernoulli
subset laws. The label construction raises the union density when `L p < 1`;
the mandatory-row construction covers every coordinate when `1 ≤ L p`.
Both cases use the same row-failure budget, without independence between rows.
-/

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The density reduction works on any finite ground set. -/
theorem original_density_small (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (D : Family α) (hD : 1 - 1 / (2 : ℝ) ^ 75 ≤ familyMeasure p D) :
    Small p (exceptional ((2 : ℕ) ^ 75) D) := by
  let L : ℕ := 2 ^ 70
  have hL : 1 < L := density_rows_gt_one
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast density_rows_pos
  have hLcast : (L : ℝ) = (2 : ℝ) ^ 70 := by
    simp only [L, Nat.cast_pow, Nat.cast_ofNat]
  have hcount : 32 * L = (2 : ℕ) ^ 75 := density_tuple_count
  have hD' : 1 - 1 / (32 * (L : ℝ)) ≤ familyMeasure p D := by
    rw [hLcast, ← density_tuple_count_real]
    exact hD
  have hbudget : (L : ℝ) * (1 - familyMeasure p D) ≤ 1 / 32 :=
    density_failure_budget hLpos hD'
  by_cases hlow : (L : ℝ) * p < 1
  · have hq0 : 0 < (L : ℝ) * p := mul_pos hLpos hp0
    have hmeasure := familyMeasure_unionFamily_label_lower L p hp0.le hlow.le D
    have hhalf : (1 / 2 : ℝ) ≤ familyMeasure ((L : ℝ) * p) (unionFamily L D) := by
      calc
        (1 / 2 : ℝ) ≤ 1 - 1 / 32 := by norm_num
        _ ≤ 1 - (L : ℝ) * (1 - familyMeasure p D) := sub_le_sub_left hbudget 1
        _ ≤ familyMeasure ((L : ℝ) * p) (unionFamily L D) := hmeasure
    have hsmall := halfDensity_small hq0 hlow (unionFamily L D) hhalf
    have hquot : ((L : ℝ) * p) / (2 : ℝ) ^ 70 = p := by
      rw [← hLcast]
      exact mul_div_cancel_left₀ p hLpos.ne'
    rw [hquot, exceptional_unionFamily, hcount] at hsmall
    exact hsmall
  · have hhigh : 1 ≤ (L : ℝ) * p := le_of_not_gt hlow
    obtain ⟨rows, hrows, hfull⟩ := exists_mandatory_cover hL p hp1 hhigh D
      (hbudget.trans_lt (by norm_num : (1 / 32 : ℝ) < 1))
    have hempty := exceptional_mul_eq_empty_of_full_union
      (a := 32) (by decide : 0 < 32) rows hrows hfull
    rw [hcount] at hempty
    rw [hempty]
    exact small_empty p

theorem talagrand_discrete_convexity (N : ℕ) (_hN : 1 ≤ N)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (D : Family (Fin N))
    (hD : 1 - 1 / (2 : ℝ) ^ 75 ≤ familyMeasure p D) :
    Small p (exceptional ((2 : ℕ) ^ 75) D) :=
  original_density_small p hp0 hp1 D hD

end TalagrandDiscreteConvexity

end OAI
