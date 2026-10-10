import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.JointSupportAnchors
import OAI.Analysis.RieszRectifiability.Flatness.ConditionedPlaneComparison

namespace OAI

/-!
Upper growth and a lower ball-mass bound provide uniformly separated joint support anchors for
two affine planes. A small joint squared fitting error then yields a quantitative comparison of
the planes, with distortion controlled by the anchor span-condition constant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

theorem exists_measured_plane_comparison_width (n d : ℕ)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧
      ∀ μ : Measure (Ambient d), IsFiniteMeasureOnCompacts μ → GlobalUpperGrowth n C μ →
      ∀ R : ℝ, 0 < R → c * R ^ n ≤ μ.real (ball (0 : Ambient d) R) →
      ∀ S W : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S → IsAffineNPlane n W →
      ∀ η : ℝ, 0 < η →
      (∫ x in ball (0 : Ambient d) R, jointPlaneFitError S W x ∂μ) ≤
        η ^ 2 * ((c / 2) * R ^ n) →
      spanConditionConstant (2 * R) (τ * R) n * (2 * η) ≤ 1 / 2 →
      ∃ a ∈ S, ‖a‖ ≤ R + η ∧ ∀ x ∈ S,
        infDist x (W : Set (Ambient d)) ≤
          2 * η * (1 + 4 * spanConditionConstant (2 * R) (τ * R) n * ‖x - a‖) := by
  obtain ⟨τ, hτ, hτ1, hanchors⟩ := exists_uniform_joint_support_anchors n d C c hC hc
  refine ⟨τ, hτ, hτ1, ?_⟩
  intro μ hfinite hg R hR hmass S W hS hW η hη herr hsmall
  let : IsFiniteMeasureOnCompacts μ := hfinite
  let : Nonempty S := hS.1.to_subtype
  obtain ⟨p0, hp0, _hsupport0, p, hp, _hsep, _hlin, hcoeff⟩ :=
    hanchors μ hfinite hg R hR hmass S W hS.1 hW.1 η hη herr
  have h0 := jointPlaneGoodSet_distance_bounds S W R η hη p0 hp0
  have hbase : infDist p0 (S : Set (Ambient d)) ≤ η ∧
      infDist p0 (W : Set (Ambient d)) ≤ η := ⟨h0.2.1.le, h0.2.2.le⟩
  have hpoints : ∀ i, infDist (p i) (S : Set (Ambient d)) ≤ η ∧
      infDist (p i) (W : Set (Ambient d)) ≤ η := by
    intro i
    have hi := jointPlaneGoodSet_distance_bounds S W R η hη (p i) (hp i).1
    exact ⟨hi.2.1.le, hi.2.2.le⟩
  let a : Ambient d := orthogonalProjection S p0
  have ha : a ∈ S := orthogonalProjection_mem p0
  have hnorm0 : ‖p0‖ ≤ R := by
    have hlt : ‖p0‖ < R := by simpa only [mem_ball, dist_zero_right] using! h0.1
    exact hlt.le
  have hnormdist : ‖p0 - a‖ ≤ η := by
    rw [← dist_eq_norm, dist_orthogonalProjection_eq_infDist]
    exact hbase.1
  have hanorm : ‖a‖ ≤ R + η :=
    (norm_le_norm_add_norm_sub p0 a).trans (add_le_add hnorm0 hnormdist)
  refine ⟨a, ha, hanorm, ?_⟩
  intro x hx
  exact plane_distance_bound_from_conditioned_support_anchors S W hS hW p0 p
    (spanConditionConstant (2 * R) (τ * R) n) η
    (spanConditionConstant_nonneg (2 * R) (τ * R) (by positivity) (mul_pos hτ hR) n)
    hη.le hsmall hcoeff hbase hpoints x hx

end

end RieszRectifiability

end OAI
