import OAI.Analysis.KadisonKastler.GraphCutScalarBounds

namespace OAI

/-! # Scalar clipping for the low logarithmic cut -/

namespace KadisonKastler

noncomputable section

def graphComplementScalar (c s : ℝ) : ℝ := 1 - s / graphScaleScalar c s

def graphLowFactorScalar (c r s : ℝ) : ℝ :=
  c ^ 2 / (graphScaleScalar c s * graphScaleScalar c r)

theorem graphComplementScalar_nonneg {c s : ℝ} (hc : c ≠ 0) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ graphComplementScalar c s := by
  apply sub_nonneg.mpr
  apply (div_le_one (graphScaleScalar_pos hc hs hs1)).mpr
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hs1))

theorem graphComplementScalar_difference {c r s : ℝ} (hc : c ≠ 0)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    graphComplementScalar c s - graphComplementScalar c r =
      graphLowFactorScalar c r s * (r - s) := by
  have hs0 := (graphScaleScalar_pos hc hs hs1).ne'
  have hr0 := (graphScaleScalar_pos hc hr hr1).ne'
  unfold graphComplementScalar graphLowFactorScalar
  field_simp
  unfold graphScaleScalar
  ring

theorem graphComplementScalar_clipping {c r s : ℝ} (hc : c ≠ 0)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    graphComplementScalar c s - min (graphComplementScalar c s) (graphComplementScalar c r) =
      graphLowFactorScalar c r s * max (r - s) 0 := by
  have hd := graphComplementScalar_difference hc hr hr1 hs hs1
  have hf : 0 ≤ graphLowFactorScalar c r s := div_nonneg (sq_nonneg _)
    (mul_nonneg (graphScaleScalar_pos hc hs hs1).le (graphScaleScalar_pos hc hr hr1).le)
  rcases le_total s r with hsr | hrs
  · have hg : graphComplementScalar c r ≤ graphComplementScalar c s := by
      apply sub_nonneg.mp
      rw [hd]
      exact mul_nonneg hf (sub_nonneg.mpr hsr)
    rw [min_eq_right hg, max_eq_left (sub_nonneg.mpr hsr), hd]
  · have hg : graphComplementScalar c s ≤ graphComplementScalar c r := by
      apply sub_nonpos.mp
      rw [hd]
      exact mul_nonpos_of_nonneg_of_nonpos hf (sub_nonpos.mpr hrs)
    rw [min_eq_left hg, sub_self, max_eq_right (sub_nonpos.mpr hrs), mul_zero]

theorem graphComplementScalar_logistic {c b : ℝ} (hc : c ≠ 0) :
    graphComplementScalar c ((1 + Real.exp b)⁻¹) =
      c ^ 2 * Real.exp b / (1 + c ^ 2 * Real.exp b) := by
  have hp : 0 < (1 + Real.exp b)⁻¹ := by positivity
  have hp1 : (1 + Real.exp b)⁻¹ ≤ 1 :=
    (inv_lt_one_of_one_lt₀ (by linarith [Real.exp_pos b])).le
  have hq := (graphScaleScalar_pos hc hp.le hp1).ne'
  have hne : 1 + c ^ 2 * Real.exp b ≠ 0 := by positivity
  have hsum : 1 + Real.exp b ≠ 0 := by positivity
  unfold graphComplementScalar
  apply (eq_div_iff hne).mpr
  field_simp
  unfold graphScaleScalar
  field_simp [hne, hsum]
  ring

theorem graphComplementScalar_exp (a : ℝ) :
    graphComplementScalar (Real.exp (-a / 2)) ((1 + Real.exp (a - 1 / 2))⁻¹) =
      Real.exp (-(1 / 2 : ℝ)) / (1 + Real.exp (-(1 / 2 : ℝ))) := by
  rw [graphComplementScalar_logistic (Real.exp_ne_zero _), graphScale_exp_square]
  have he : Real.exp (-a) * Real.exp (a - 1 / 2) = Real.exp (-(1 / 2 : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]

end

end KadisonKastler

end OAI
