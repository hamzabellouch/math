import OAI.Geometry.RCD.Heat.FinitePrefixEnvelope
import OAI.Geometry.RCD.Heat.SlowHeatGrowth

namespace OAI

/-! # Starting the cumulative argument at any positive heat metric -/

open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every positive invertible heat metric has finite two-sided inverse
comparison constants, even before choosing a normalized initial frame. -/
theorem positive_equiv_inverse_comparison (Q : E ≃L[ℝ] E)
    (hQ : (Q : E →L[ℝ] E).IsPositive) (v : E) :
    ⟪v, Q.symm v⟫_ℝ ≤ ‖(Q.symm : E →L[ℝ] E)‖ * ‖v‖ ^ 2 ∧
      ‖v‖ ^ 2 ≤ ‖(Q : E →L[ℝ] E)‖ * ⟪v, Q.symm v⟫_ℝ := by
  refine ⟨quadratic_le_opNorm (Q.symm : E →L[ℝ] E) v, ?_⟩
  have hp := (positive_equiv_symm Q hQ).inner_nonneg_right v
  have hcs := positive_form_cauchy_schwarz hQ (Q.symm v) v
  have hinner : ⟪Q.symm v, Q v⟫_ℝ = ‖v‖ ^ 2 := by
    have h := hQ.inner_left_eq_inner_right (Q.symm v) v
    change ⟪Q (Q.symm v), v⟫_ℝ = ⟪Q.symm v, Q v⟫_ℝ at h
    rw [Q.apply_symm_apply, real_inner_self_eq_norm_sq] at h
    exact h.symm
  have he : ⟪Q.symm v, v⟫_ℝ = ⟪v, Q.symm v⟫_ℝ := real_inner_comm _ _
  simp only [ContinuousLinearEquiv.coe_coe] at hcs
  rw [hinner, Q.apply_symm_apply, he] at hcs
  have hupper := mul_le_mul_of_nonneg_left (quadratic_le_opNorm (Q : E →L[ℝ] E) v) hp
  simp only [ContinuousLinearEquiv.coe_coe] at hupper
  by_cases hv : v = 0
  · simp [hv]
  have hpos : 0 < ‖v‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
  nlinarith only [hcs, hupper, hpos]

/-- Slow adjacent growth propagates any finite initial coercivity
constant to the squared norm of all inverse metrics. -/
theorem inverse_norm_sq_of_slow_growth_coercive (Q : ℕ → E ≃L[ℝ] E)
    {B : ℝ} (hB : 0 ≤ B)
    (hstep : ∀ i v, ⟪v, Q i v⟫_ℝ ≤ (9 / 8 : ℝ) * ⟪v, Q (i + 1) v⟫_ℝ)
    (hbase : ∀ v, ‖v‖ ^ 2 ≤ B * ⟪v, Q 0 v⟫_ℝ) (i : ℕ) (v : E) :
    ‖(Q i).symm v‖ ^ 2 ≤ B ^ 2 * (81 / 64 : ℝ) ^ i * ‖v‖ ^ 2 := by
  let w := (Q i).symm v
  have hg := geometric_form_growth (fun j => (Q j : E →L[ℝ] E))
    (by norm_num : (0 : ℝ) ≤ 9 / 8) hstep (Nat.zero_le i) w
  simp only [Nat.sub_zero, ContinuousLinearEquiv.coe_coe] at hg
  have hw : Q i w = v := (Q i).apply_symm_apply v
  rw [hw] at hg
  have hb := (hbase w).trans (mul_le_mul_of_nonneg_left hg hB)
  have hcs := real_inner_le_norm w v
  have hc : 0 ≤ B * (9 / 8 : ℝ) ^ i := by positivity
  have hbound : ‖w‖ ≤ B * (9 / 8 : ℝ) ^ i * ‖v‖ := by
    by_cases hz : ‖w‖ = 0
    · rw [hz]; positivity
    have hp : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hh := mul_le_mul_of_nonneg_left hcs hc
    nlinarith only [hb, hh, hp]
  have hs := pow_le_pow_left₀ (norm_nonneg w) hbound 2
  have hpow : ((9 / 8 : ℝ) ^ i) ^ 2 = (81 / 64 : ℝ) ^ i := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  calc
    _ ≤ (B * (9 / 8 : ℝ) ^ i * ‖v‖) ^ 2 := hs
    _ = _ := by rw [mul_pow, mul_pow, hpow]

end RegularPointCoordinates

end

end OAI
