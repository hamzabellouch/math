import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousInverseWeight

namespace OAI

/-! # The inverse-weight moment needed for classical second derivatives

In dimension twelve, k > 8 makes |xi|⁴ divided by the Y weight integrable.
At the origin the factor |xi|⁴ only improves the existing inverse-weight
estimate. This is the exact moment required for the physical C² bridge.
-/

open MeasureTheory Set

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem homogeneous_secondMoment_high_bound (a k : ℝ) (ξ : E) (hξ : ξ ≠ 0) :
    ‖ξ‖ ^ 4 * (homogeneousFourierWeight a k ξ)⁻¹ ≤
      (2 * Real.pi) ^ (12 : ℕ) * ‖ξ‖ ^ (4 - 2 * k : ℝ) := by
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hp : 0 < ((2 * Real.pi) ^ (12 : ℕ))⁻¹ * ‖ξ‖ ^ (2 * k) := by positivity
  have hw : ((2 * Real.pi) ^ (12 : ℕ))⁻¹ * ‖ξ‖ ^ (2 * k) ≤
      homogeneousFourierWeight a k ξ :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)
  calc
    _ ≤ ‖ξ‖ ^ 4 * (((2 * Real.pi) ^ (12 : ℕ))⁻¹ * ‖ξ‖ ^ (2 * k))⁻¹ :=
      mul_le_mul_of_nonneg_left (inv_anti₀ hp hw) (by positivity)
    _ = (2 * Real.pi) ^ (12 : ℕ) * (‖ξ‖ ^ (4 : ℝ) * ‖ξ‖ ^ (-(2 * k))) := by
      simp only [mul_inv_rev, inv_inv, Real.rpow_neg hn.le, Real.rpow_ofNat]
      ring
    _ = _ := by rw [← Real.rpow_add hn]; congr 2

theorem integrable_homogeneousSecondMomentWeight (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    Integrable (fun ξ : E => ‖ξ‖ ^ 4 * (homogeneousFourierWeight a k ξ)⁻¹) := by
  have hm : AEStronglyMeasurable
      (fun ξ : E => ‖ξ‖ ^ 4 * (homogeneousFourierWeight a k ξ)⁻¹) volume :=
    (continuous_norm.pow 4).aestronglyMeasurable.mul
      (continuous_homogeneousFourierWeight a k ha1 hk).measurable.inv.aestronglyMeasurable
  have hsmall : IntegrableOn
      (fun ξ : E => ‖ξ‖ ^ 4 * (homogeneousFourierWeight a k ξ)⁻¹) (Metric.ball 0 1) := by
    apply (integrable_homogeneousFourierWeight_inv a k ha ha1 hk).integrableOn.mono' hm.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball] with ξ hξ
    have hn : ‖ξ‖ ≤ 1 := (by simpa only [Metric.mem_ball, dist_zero_right] using hξ : ‖ξ‖ < 1).le
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (by positivity) (inv_nonneg.mpr (homogeneousFourierWeight_nonneg a k ξ)))]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (homogeneousFourierWeight_nonneg a k ξ))
      (pow_le_one₀ (norm_nonneg _) hn)
  have hbase : Integrable (fun ξ : E => (1 + ‖ξ‖) ^ (4 - 2 * k : ℝ)) := by
    rw [show (4 - 2 * k : ℝ) = -(2 * k - 4) by ring]
    apply integrable_one_add_norm
    norm_num
    linarith
  have hlarge : IntegrableOn
      (fun ξ : E => ‖ξ‖ ^ 4 * (homogeneousFourierWeight a k ξ)⁻¹) (Metric.ball 0 1)ᶜ := by
    apply ((hbase.const_mul ((2 * Real.pi) ^ (12 : ℕ) * 2 ^ (2 * k - 4))).integrableOn).mono'
      hm.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with ξ hξ
    have hn : 1 ≤ ‖ξ‖ := by
      simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hξ
    have hξ0 : ξ ≠ 0 := by intro h; simp only [h, norm_zero] at hn; linarith
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (by positivity) (inv_nonneg.mpr (homogeneousFourierWeight_nonneg a k ξ)))]
    calc
      _ ≤ (2 * Real.pi) ^ (12 : ℕ) * ‖ξ‖ ^ (4 - 2 * k : ℝ) :=
        homogeneous_secondMoment_high_bound a k ξ hξ0
      _ ≤ (2 * Real.pi) ^ (12 : ℕ) * ((1 + ‖ξ‖) / 2) ^ (4 - 2 * k : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)) (by positivity)
      _ = _ := by
        rw [Real.div_rpow (by positivity) (by positivity)]
        rw [show (4 - 2 * k : ℝ) = -(2 * k - 4) by ring, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2),
          div_inv_eq_mul]
        ring
  simpa only [union_compl_self, integrableOn_univ] using hsmall.union hlarge

end DefocusingNLS

end OAI
