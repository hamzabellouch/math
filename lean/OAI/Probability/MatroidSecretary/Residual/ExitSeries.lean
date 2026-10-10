import OAI.Probability.MatroidProphet.Main
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

namespace MatroidProphet

/-- Exact sum of all hazard-band bounds beginning at any natural level. -/
theorem hasSum_hazardBandBound (start : ℕ) :
    HasSum (fun k : ℕ => hazardBandBound (start + k)) (hazardTailPotential start) := by
  have hn : HasSum (fun k : ℕ => (k : ℝ) * ((1 : ℝ) / 2) ^ k) 2 := by
    have h := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 : ℝ) / 2)
      (by norm_num)
    norm_num at h
    exact h
  have h := ((hn.mul_left (Real.log 2)).add
    (hasSum_geometric_two.mul_left (((start : ℝ) + 1) * Real.log 2 + 1))).div_const
      ((2 : ℝ) ^ start)
  have heq : (fun k : ℕ => hazardBandBound (start + k)) =
      (fun k : ℕ => (Real.log 2 * ((k : ℝ) * ((1 : ℝ) / 2) ^ k) +
        (((start : ℝ) + 1) * Real.log 2 + 1) * ((1 : ℝ) / 2) ^ k) / (2 : ℝ) ^ start) := by
    funext k
    unfold hazardBandBound
    push_cast
    rw [pow_add]
    simp only [div_pow, one_pow]
    field_simp
    ring
  rw [heq]
  have hc : hazardTailPotential start =
      (Real.log 2 * 2 + (((start : ℝ) + 1) * Real.log 2 + 1) * 2) / (2 : ℝ) ^ start := by
    unfold hazardTailPotential
    ring
  rw [hc]
  exact h

/-- The infinite dyadic tail equals the source's explicit resource bound. -/
theorem tsum_hazardBandBound (start : ℕ) :
    (∑' k : ℕ, hazardBandBound (start + k)) = hazardTailPotential start :=
  (hasSum_hazardBandBound start).tsum_eq

/-- Source equation `eq:dyadic-exit`, including its strict numerical bound. -/
theorem dyadic_exit_series :
    (∑' k : ℕ, hazardBandBound (12 + k)) =
      ((2 : ℝ) ^ 11)⁻¹ * (14 * Real.log 2 + 1) ∧
    (∑' k : ℕ, hazardBandBound (12 + k)) < (1 : ℝ) / 2 := by
  rw [tsum_hazardBandBound]
  refine ⟨?_, hazardTailPotential_twelve⟩
  norm_num [hazardTailPotential]
  ring

end MatroidProphet

end OAI
