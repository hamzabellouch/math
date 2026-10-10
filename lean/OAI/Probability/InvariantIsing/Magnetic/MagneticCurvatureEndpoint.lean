import OAI.Probability.InvariantIsing.Magnetic.MagneticCurvatureBound

namespace OAI

/-! A continuous closed-interval curvature representative, obtained
from the actual spin-variance bound rather than an asymptotic expansion. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

def closedMagneticCurvature (h : FieldStep) (s : ℝ) : ℝ :=
  if |s| < 1 then magneticCurvature h s else 0

lemma closedMagneticCurvature_nonneg (h : FieldStep) (s : ℝ) :
    0 ≤ closedMagneticCurvature h s := by
  unfold closedMagneticCurvature
  split_ifs with hs
  · exact (magneticCurvature_pos h s).le
  · exact le_rfl

lemma closedMagneticCurvature_le_spin_variance (h : FieldStep) {s : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) : closedMagneticCurvature h s ≤ 1 - s ^ 2 := by
  unfold closedMagneticCurvature
  split_ifs with hi
  · exact magneticCurvature_le_spin_variance h hi
  · have hp := mul_nonneg (by linarith [hs.1] : 0 ≤ s + 1)
      (by linarith [hs.2] : 0 ≤ 1 - s)
    nlinarith

lemma closedMagneticCurvature_eq (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    closedMagneticCurvature h s = magneticCurvature h s := ite_eq_left hs

lemma continuousWithinAt_closedMagneticCurvature_endpoint (h : FieldStep)
    {s : ℝ} (hs : |s| = 1) :
    ContinuousWithinAt (closedMagneticCurvature h) (Icc (-1 : ℝ) 1) s := by
  have hs2 : s ^ 2 = 1 := by nlinarith [sq_abs s]
  have he : closedMagneticCurvature h s = 0 := by
    simp only [closedMagneticCurvature, hs, lt_self_iff_false, ite_false]
  have hg : Tendsto (fun t : ℝ => 1 - t ^ 2) (𝓝[Icc (-1 : ℝ) 1] s) (𝓝 0) := by
    have hc : ContinuousWithinAt (fun t : ℝ => 1 - t ^ 2) (Icc (-1 : ℝ) 1) s :=
      (show ContinuousAt (fun t : ℝ => 1 - t ^ 2) s by fun_prop).continuousWithinAt
    change Tendsto (fun t : ℝ => 1 - t ^ 2) (𝓝[Icc (-1 : ℝ) 1] s) (𝓝 (1 - s ^ 2)) at hc
    simpa only [hs2, sub_self] using hc
  change Tendsto (closedMagneticCurvature h) (𝓝[Icc (-1 : ℝ) 1] s)
    (𝓝 (closedMagneticCurvature h s))
  rw [he]
  apply squeeze_zero' (Filter.Eventually.of_forall (closedMagneticCurvature_nonneg h)) ?_ hg
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact closedMagneticCurvature_le_spin_variance h ht

lemma continuousOn_closedMagneticCurvature (h : FieldStep) :
    ContinuousOn (closedMagneticCurvature h) (Icc (-1 : ℝ) 1) := by
  intro s hs
  by_cases hi : |s| < 1
  · have he : closedMagneticCurvature h =ᶠ[𝓝 s] magneticCurvature h := by
      filter_upwards [Ioo_mem_nhds (abs_lt.mp hi).1 (abs_lt.mp hi).2] with t ht
      exact closedMagneticCurvature_eq h (abs_lt.mpr ht)
    exact ((hasDerivAt_magneticCurvature h hi).continuousAt.congr_of_eventuallyEq he).continuousWithinAt
  · have ha : |s| ≤ 1 := abs_le.mpr hs
    exact continuousWithinAt_closedMagneticCurvature_endpoint h (le_antisymm ha (le_of_not_gt hi))

end InvariantIsing

end

end OAI
