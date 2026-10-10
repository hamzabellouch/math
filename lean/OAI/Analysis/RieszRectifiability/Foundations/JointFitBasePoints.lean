import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.NonconcentrationPoint
import OAI.Analysis.RieszRectifiability.Flatness.JointPlaneGoodSet

namespace OAI

/-!
# Bounded base points for jointly fitting planes

A lower mass bound and a small integral joint-fit error produce a point close
to both affine planes. Orthogonal projection of that point supplies base points
on each plane with norm bounded by the ball radius plus the fitting tolerance.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry
open scoped ENNReal

theorem exists_small_norm_points_on_joint_fits {n d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (S W : AffineSubspace ℝ (Ambient d))
    (hS : (S : Set (Ambient d)).Nonempty) (hW : (W : Set (Ambient d)).Nonempty)
    (R η c : ℝ) (hR : 0 < R) (hη : 0 < η) (hc : 0 < c)
    (hmass : c * R ^ n ≤ μ.real (ball (0 : Ambient d) R))
    (herr : (∫ x in ball (0 : Ambient d) R, jointPlaneFitError S W x ∂μ) ≤
      η ^ 2 * ((c / 2) * R ^ n)) :
    (∃ a ∈ S, ‖a‖ ≤ R + η) ∧ (∃ b ∈ W, ‖b‖ ≤ R + η) := by
  have hm := jointPlaneGoodSet_mass_lower μ S W hS hW R η c hη hmass herr
  have hpos : 0 < μ.real (jointPlaneGoodSet S W R η) :=
    (mul_pos (by positivity : 0 < c / 2) (pow_pos hR n)).trans_le hm
  obtain ⟨x, hx, _hsupport, _hout⟩ := exists_support_point_outside_small_set μ
    (jointPlaneGoodSet S W R η) ∅ (by simp) (by simpa only [measureReal_empty] using! hpos)
  have hbounds := jointPlaneGoodSet_distance_bounds S W R η hη x hx
  have hxnorm : ‖x‖ ≤ R := by
    have hlt : ‖x‖ < R := by simpa only [mem_ball, dist_zero_right] using! hbounds.1
    exact hlt.le
  have hpoint : ∀ T : AffineSubspace ℝ (Ambient d), (T : Set (Ambient d)).Nonempty →
      infDist x (T : Set (Ambient d)) ≤ η → ∃ a ∈ T, ‖a‖ ≤ R + η := by
    intro T hT hfit
    let : Nonempty T := hT.to_subtype
    let a : Ambient d := orthogonalProjection T x
    have herror : ‖x - a‖ ≤ η := by
      rw [← dist_eq_norm, dist_orthogonalProjection_eq_infDist]
      exact hfit
    exact ⟨a, orthogonalProjection_mem x,
      (norm_le_norm_add_norm_sub x a).trans (add_le_add hxnorm herror)⟩
  exact ⟨hpoint S hS hbounds.2.1.le, hpoint W hW hbounds.2.2.le⟩

end

end RieszRectifiability

end OAI
