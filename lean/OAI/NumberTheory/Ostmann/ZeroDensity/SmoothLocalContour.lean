import Mathlib.Analysis.Complex.CauchyIntegral
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothContourResidue

namespace OAI

/-! # Small-circle integrals around the actual character zeros -/

namespace Ostmann

open Filter Metric Set MeasureTheory
open scoped Topology

theorem PrimitiveComplexCharacter.exists_zero_free_punctured_ball
    (χ : PrimitiveComplexCharacter) (z : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ w ∈ closedBall z r, w ≠ z → χ.L w ≠ 0 := by
  obtain ⟨g, hg, hgne, he⟩ := (χ.L_analytic z).analyticOrderAt_ne_top.mp (χ.L_order_ne_top z)
  have hgood : ∀ᶠ w in 𝓝 z, w ≠ z → χ.L w ≠ 0 := by
    filter_upwards [he, hg.continuousAt.eventually_ne hgne] with w hw hgw hwz
    rw [hw, smul_eq_mul]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hwz)) hgw
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hgood
  refine ⟨r / 2, by positivity, ?_⟩
  intro w hw hwz
  apply hball (lt_of_le_of_lt (mem_closedBall.mp hw) (by linarith)) hwz

theorem smoothContour_small_circle (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (z : ℂ) :
    ∃ r : ℝ, 0 < r ∧
      (∮ s in C(z, r), (-deriv χ.L s / χ.L s) * smoothContourWeight X s) =
        (2 * (Real.pi : ℂ) * Complex.I) *
          (-(analyticOrderNatAt χ.L z : ℂ) * smoothContourWeight X z) := by
  obtain ⟨r, hr, hno⟩ := χ.exists_zero_free_punctured_ball z
  let F : ℂ → ℂ := fun s => (s - z) * ((-deriv χ.L s / χ.L s) * smoothContourWeight X s)
  have hF (w : ℂ) (hw : w ∈ closedBall z r) (hwz : w ≠ z) : AnalyticAt ℂ F w := by
    have hL := χ.L_analytic w
    have hW := (smoothContourWeight_differentiable X hX).analyticAt w
    exact (analyticAt_id.sub analyticAt_const).mul ((hL.deriv.neg.div hL (hno w hw hwz)).mul hW)
  have hc : ContinuousOn F (closedBall z r \ {z}) := fun w hw =>
    (hF w hw.1 hw.2).continuousAt.continuousWithinAt
  have hd : ∀ w ∈ (ball z r \ {z}) \ (∅ : Set ℂ), DifferentiableAt ℂ F w := by
    intro w hw
    exact (hF w (ball_subset_closedBall hw.1.1) hw.1.2).differentiableAt
  have hi := Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
    hr Set.countable_empty hc hd (smoothContour_zero_residue χ X hX z)
  refine ⟨r, hr, ?_⟩
  calc
    _ = ∮ s in C(z, r), (s - z)⁻¹ • F s := by
      apply circleIntegral.integral_congr hr.le
      intro s hs
      have hsz : s - z ≠ 0 := sub_ne_zero.mpr (by
        intro he
        subst s
        have hh : (0 : ℝ) = r := by simpa using hs
        linarith)
      simp [F, smul_eq_mul, ← mul_assoc, hsz]
    _ = _ := by simpa only [smul_eq_mul] using hi

end Ostmann

end OAI
