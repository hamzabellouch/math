import OAI.Geometry.CylinderCovering.Caps.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Radial.Riemann
import OAI.Geometry.CylinderCovering.Caps.FiniteArea

namespace OAI

noncomputable section
namespace CylinderCovering.HalfheightFinite
open Set Filter MeasureTheory
open scoped Topology

lemma midpoint_isTagged (N : ℕ) :
    RadialRiemann.IsTagged (-1) 1 N (midpoint N) := by
  intro i
  have hd := RadialRiemann.step_pos (by norm_num : (-1 : ℝ) < 1)
    (Nat.zero_lt_of_lt i.isLt)
  have hs := RadialRiemann.point_succ (-1) 1 N i
  change RadialRiemann.point (-1) 1 N i ≤ midpoint N i ∧
    midpoint N i ≤ RadialRiemann.point (-1) 1 N (i+1)
  dsimp [midpoint]
  constructor <;> linarith

lemma projectionWeight_continuous (δ : ℝ) :
    Continuous (fun r : ℝ =>
      1 / Real.sqrt (1 + δ^2 * (alpha r^2 + 2 * beta r^2))) := by
  apply continuous_const.div
    (show Continuous (fun r : ℝ =>
      Real.sqrt (1 + δ^2 * (alpha r^2 + 2 * beta r^2))) by
      unfold alpha beta
      fun_prop)
  intro r
  apply ne_of_gt
  apply Real.sqrt_pos.mpr
  positivity

theorem localArea_sum_tendsto (δ : ℝ) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1 : ℝ) 1)) :
    Tendsto (fun N => ∑ i : Fin N, localArea δ R N i) atTop
      (𝓝 (limitingArea δ R / 2)) := by
  have h := RadialRiemann.maxPolynomialSum_tendsto
    (by norm_num : (-1 : ℝ) < 1) hR
    (projectionWeight_continuous δ).continuousOn
    (height/4) (3*height*δ/8) (height*δ^2/8)
    midpoint midpoint_isTagged
  convert h using 1
  · funext N
    apply Finset.sum_congr rfl
    intro i _
    simp only [localArea, maxCap, collar, halfwidth, RadialRiemann.step]
    ring
  · unfold limitingArea
    have hi : (∫ r in (-1 : ℝ)..1,
        R r^2 / Real.sqrt (1+δ^2*(alpha r^2+2*beta r^2))) =
        ∫ r in (-1 : ℝ)..1,
          R r^2 * (1 / Real.sqrt (1+δ^2*(alpha r^2+2*beta r^2))) := by
      apply intervalIntegral.integral_congr
      intro r _
      ring
    rw [hi]
    congr 1
    ring

theorem totalArea_tendsto {δ : ℝ} (hδ : 0 ≤ δ) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1 : ℝ) 1))
    (hR0 : ∀ r ∈ Icc (-1 : ℝ) 1, 0 ≤ R r) :
    Tendsto (totalArea δ R) atTop (𝓝 (limitingArea δ R)) := by
  have h := (localArea_sum_tendsto δ hR).const_mul 2
  simpa only [← totalArea_eq_two_sum hδ hR hR0, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using h

end CylinderCovering.HalfheightFinite

end

end OAI
