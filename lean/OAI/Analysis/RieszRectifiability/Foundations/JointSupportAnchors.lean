import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.GreedyAffineAnchors
import OAI.Analysis.RieszRectifiability.Flatness.JointPlaneGoodSet
import OAI.Analysis.RieszRectifiability.Foundations.LargeSubsetEscape

namespace OAI

/-!
Joint plane-fit control and uniform affine escape produce support anchors with quantitative
spanning bounds. The separation parameter is chosen uniformly before the measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators ENNReal

theorem exists_uniform_joint_support_anchors (n d : ℕ)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧
      ∀ μ : Measure (Ambient d), IsFiniteMeasureOnCompacts μ → GlobalUpperGrowth n C μ →
      ∀ R : ℝ, 0 < R → c * R ^ n ≤ μ.real (ball (0 : Ambient d) R) →
      ∀ S W : AffineSubspace ℝ (Ambient d), (S : Set (Ambient d)).Nonempty →
      (W : Set (Ambient d)).Nonempty → ∀ η : ℝ, 0 < η →
      (∫ x in ball (0 : Ambient d) R, jointPlaneFitError S W x ∂μ) ≤
        η ^ 2 * ((c / 2) * R ^ n) →
      ∃ p0 ∈ jointPlaneGoodSet S W R η, p0 ∈ μ.support ∧
        ∃ p : Fin n → Ambient d,
          (∀ i, p i ∈ jointPlaneGoodSet S W R η ∧ p i ∈ μ.support) ∧
          OrderedSpanSeparated n (fun i => p i - p0) (τ * R) ∧
          LinearIndependent ℝ (fun i => p i - p0) ∧
          ∀ t : Fin n → ℝ, (∑ i, |t i|) ≤
            spanConditionConstant (2 * R) (τ * R) n * ‖∑ i, t i • (p i - p0)‖ := by
  obtain ⟨τ, hτ, hτ1, hescape⟩ := exists_uniform_affine_escape_width_for_subsets
    n d C (c / 2) hC (by positivity)
  refine ⟨τ, hτ, hτ1, ?_⟩
  intro μ hfinite hg R hR hmass S W hS hW η hη herr
  let : IsFiniteMeasureOnCompacts μ := hfinite
  let s := jointPlaneGoodSet S W R η
  have hs : s ⊆ ball (0 : Ambient d) R := inter_subset_left
  have hsmass : (c / 2) * R ^ n ≤ μ.real s :=
    jointPlaneGoodSet_mass_lower μ S W hS hW R η c hη hmass herr
  have hpos : 0 < μ.real s := (mul_pos (by positivity : 0 < c / 2) (pow_pos hR n)).trans_le hsmass
  obtain ⟨p0, hp0, hp0support, _hout⟩ := exists_support_point_outside_small_set μ s ∅
    (by simp) (by simpa only [measureReal_empty] using! hpos)
  let good := s ∩ μ.support
  have hgood : good ⊆ ball (0 : Ambient d) R := fun _ hx => hs hx.1
  have he : ∀ k : ℕ, k < n → ∀ T : AffineSubspace ℝ (Ambient d), IsAffineNPlane k T →
      ∃ x ∈ good, τ * R ≤ infDist x (T : Set (Ambient d)) := by
    intro k hkn T hT
    obtain ⟨x, hx, hxsupport, hxr⟩ := hescape μ hg R hR s hs hsmass k hkn T hT
    exact ⟨x, ⟨hx, hxsupport⟩, hxr⟩
  obtain ⟨p, hp, hsep, hlin, hcoeff⟩ := exists_conditioned_anchors_from_escape
    good p0 R (τ * R) hR.le (mul_pos hτ hR) hgood ⟨hp0, hp0support⟩ he
  exact ⟨p0, hp0, hp0support, p, hp, hsep, hlin, hcoeff⟩

end

end RieszRectifiability

end OAI
