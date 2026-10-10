import OAI.Analysis.KadisonKastler.GraphScaleFunctionalCalculus

namespace OAI

/-! # Scalar functions for the separated graph cuts -/

namespace KadisonKastler

noncomputable section

/-- The inverse of the complementary graph resolvent, clipped at the cut. -/
def graphHighInverseScalar (c r s : ℝ) : ℝ :=
  graphScaleScalar c (min s r) / (c ^ 2 * (1 - min s r))

theorem graphHighInverseScalar_nonneg {c r s : ℝ} (hc : c ≠ 0)
    (hr : 0 ≤ r) (hr1 : r < 1) (hs : 0 ≤ s) : 0 ≤ graphHighInverseScalar c r s := by
  have hm : 0 ≤ min s r := le_min hs hr
  have hm1 : min s r < 1 := (min_le_right s r).trans_lt hr1
  exact div_nonneg (graphScaleScalar_pos hc hm hm1.le).le
    (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hm1.le))

theorem graphHighInverseScalar_bound {c r s : ℝ} (hc : c ≠ 0)
    (hr : 0 ≤ r) (hr1 : r < 1) (hs : 0 ≤ s) :
    graphHighInverseScalar c r s ≤ graphScaleScalar c r / (c ^ 2 * (1 - r)) := by
  have hm : 0 ≤ min s r := le_min hs hr
  have hm1 : min s r < 1 := (min_le_right s r).trans_lt hr1
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hd : 0 < c ^ 2 * (1 - r) := mul_pos hc2 (sub_pos.mpr hr1)
  have hdm : 0 < c ^ 2 * (1 - min s r) := mul_pos hc2 (sub_pos.mpr hm1)
  apply (div_le_div_iff₀ hdm hd).mpr
  unfold graphScaleScalar
  nlinarith [mul_nonneg hc2.le (sub_nonneg.mpr (min_le_right s r))]

theorem graphHighInverseScalar_continuousOn {c r : ℝ} (hc : c ≠ 0)
    (hr1 : r < 1) : ContinuousOn (graphHighInverseScalar c r) (Set.Icc (0 : ℝ) 1) := by
  apply ContinuousOn.div (by unfold graphScaleScalar; fun_prop) (by fun_prop)
  intro s _
  exact mul_ne_zero (pow_ne_zero _ hc) (ne_of_gt (sub_pos.mpr ((min_le_right s r).trans_lt hr1)))

theorem graphHighInverseScalar_cut_identity {c r s : ℝ} (hc : c ≠ 0)
    (hr1 : r < 1) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (((1 - s / graphScaleScalar c s) * graphHighInverseScalar c r s) - 1) *
      max (r - s) 0 = 0 := by
  by_cases hsr : s < r
  · have hq := (graphScaleScalar_pos hc hs hs1).ne'
    have hd : c ^ 2 * (1 - s) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hc) (ne_of_gt (sub_pos.mpr (hsr.trans hr1)))
    rw [graphHighInverseScalar, min_eq_left hsr.le]
    have he : (1 - s / graphScaleScalar c s) *
        (graphScaleScalar c s / (c ^ 2 * (1 - s))) = 1 := by
      field_simp [hq, pow_ne_zero _ hc, (sub_pos.mpr (hsr.trans hr1)).ne']
      unfold graphScaleScalar
      ring
    rw [he, sub_self, zero_mul]
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt hsr)), mul_zero]

theorem graphScale_exp_square (a : ℝ) : Real.exp (-a / 2) ^ 2 = Real.exp (-a) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

theorem graphHighInverse_bound_exp (a : ℝ) :
    graphScaleScalar (Real.exp (-a / 2)) ((1 + Real.exp (a + 1 / 2))⁻¹) /
      (Real.exp (-a / 2) ^ 2 * (1 - (1 + Real.exp (a + 1 / 2))⁻¹)) =
      1 + Real.exp (-(1 / 2 : ℝ)) := by
  have he : Real.exp (-a) * Real.exp (a + 1 / 2) = Real.exp (1 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hhalf : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hp : 1 + Real.exp (a + 1 / 2) ≠ 0 := by positivity
  have hd : Real.exp (-a) * (1 - (1 + Real.exp (a + 1 / 2))⁻¹) ≠ 0 := by
    apply mul_ne_zero (Real.exp_ne_zero _)
    exact ne_of_gt (sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith [Real.exp_pos (a + 1 / 2)])))
  unfold graphScaleScalar
  rw [graphScale_exp_square]
  apply (div_eq_iff hd).mpr
  field_simp
  have harg : (a * 2 + 1) / 2 = a + 1 / 2 := by ring
  have hprod : Real.exp (-a) * Real.exp ((a * 2 + 1) / 2) * Real.exp (-(1 / 2 : ℝ)) = 1 := by
    rw [harg, he, mul_comm, hhalf]
  nlinarith [hprod]

end

end KadisonKastler

end OAI
