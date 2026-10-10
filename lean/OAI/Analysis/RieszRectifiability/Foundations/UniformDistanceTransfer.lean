import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.UniformMeasuredPlaneComparison
import OAI.Analysis.RieszRectifiability.Foundations.JointFitBasePoints
import OAI.Analysis.RieszRectifiability.Flatness.PlaneDistanceTransfer

namespace OAI

/-!
Uniform measured plane comparison transfers distance estimates from one affine plane to
another. A small-norm point on the joint fits anchors the comparison, giving an additive error
controlled by the fit scale and the normalized distance from the origin.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_uniform_measured_distance_transfer (n d : ℕ)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ A ε : ℝ, 0 < A ∧ 0 < ε ∧ ε ≤ 1 ∧
      ∀ μ : Measure (Ambient d), IsFiniteMeasureOnCompacts μ → GlobalUpperGrowth n C μ →
      ∀ R : ℝ, 0 < R → c * R ^ n ≤ μ.real (ball (0 : Ambient d) R) →
      ∀ S W : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S → IsAffineNPlane n W →
      ∀ η : ℝ, 0 < η → η ≤ ε * R →
      (∫ x in ball (0 : Ambient d) R, jointPlaneFitError S W x ∂μ) ≤
        η ^ 2 * ((c / 2) * R ^ n) →
      ∀ x : Ambient d, infDist x (W : Set (Ambient d)) ≤
        infDist x (S : Set (Ambient d)) + A * η * (3 + ‖x‖ / R) := by
  obtain ⟨A, ε, hA, hε, hε1, hcompare⟩ := exists_uniform_measured_plane_comparison n d C c hC hc
  refine ⟨A, ε, hA, hε, hε1, ?_⟩
  intro μ hfinite hg R hR hmass S W hS hW η hη hηsmall herr x
  let : IsFiniteMeasureOnCompacts μ := hfinite
  let : Nonempty S := hS.1.to_subtype
  obtain ⟨⟨a, ha, hanorm⟩, _hb⟩ := exists_small_norm_points_on_joint_fits
    μ S W hS.1 hW.1 R η c hR hη hc hmass herr
  have hηR : η ≤ R := hηsmall.trans
    ((mul_le_mul_of_nonneg_right hε1 hR.le).trans_eq (one_mul R))
  have haB : ‖a‖ ≤ 2 * R := by linarith
  have hfit := hcompare μ hfinite hg R hR hmass S W hS hW η hη hηsmall herr
  have h := plane_distance_transfer S (W : Set (Ambient d)) a ha (2 * R) (A * η) R
    (mul_nonneg hA.le hη.le) hR haB hfit x
  have heq : 1 + (‖x‖ + 2 * R) / R = 3 + ‖x‖ / R := by
    rw [add_div, mul_div_cancel_right₀ 2 hR.ne']
    ring
  simpa only [heq] using! h

end

end RieszRectifiability

end OAI
