import OAI.Geometry.IsometricImmersion.Darboux.QFirstJetFunctions

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem qFirst_segment_distance_le (a b : QFirstInput) {x : QFirstInput}
    (hx : x ∈ segment ℝ a b) : ‖x-a‖ ≤ ‖b-a‖ := by
  have hball : x ∈ Metric.closedBall a ‖b-a‖ :=
    (convex_closedBall a ‖b-a‖).segment_subset
      (by simp) (by simp only [Metric.mem_closedBall,dist_eq_norm,le_refl]) hx
  simpa only [Metric.mem_closedBall,dist_eq_norm] using hball

theorem qFirst_close_segment_subset_baseTube (a b : QFirstInput) {B d : ℝ}
    (ha : ‖a‖ ≤ B) (hdet : d ≤ qFirstDet a) (hdist : ‖b-a‖ ≤ 1)
    (hsmall : (4*max B 0+2)*‖b-a‖ ≤ d/2) :
    segment ℝ a b ⊆ qFirstBaseTube (max B 0+1) (d/2) := by
  intro x hx
  have hxa := qFirst_segment_distance_le a b hx
  have hxnorm : ‖x‖ ≤ max B 0+1 := by
    calc
      _ = ‖(x-a)+a‖ := by rw [sub_add_cancel]
      _ ≤ ‖x-a‖+‖a‖ := norm_add_le _ _
      _ ≤ 1+max B 0 := add_le_add (hxa.trans hdist) (ha.trans (le_max_left _ _))
      _ = _ := by ring
  have hmatrixD : ‖x.1.1-a.1.1‖ ≤ ‖b-a‖ :=
    (show ‖x.1.1-a.1.1‖ ≤ ‖x-a‖ from
      (norm_fst_le (x-a).1).trans (norm_fst_le (x-a))).trans hxa
  have hmatrixA : ‖a.1.1‖ ≤ max B 0 :=
    ((norm_fst_le a.1).trans (norm_fst_le a)).trans (ha.trans (le_max_left _ _))
  have hdetdiff := det_sub_le_small_first_distance (Matrix.of a.1.1) (Matrix.of x.1.1)
    (le_max_right B 0) (norm_nonneg _) hdist hmatrixA hmatrixD
  have hxdet : d/2 ≤ qFirstDet x := by
    have hneg := neg_abs_le (qFirstDet x-qFirstDet a)
    change |qFirstDet x-qFirstDet a| ≤ (4*max B 0+2)*‖b-a‖ at hdetdiff
    linarith [hdetdiff.trans hsmall]
  exact ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hxnorm,hxdet⟩

theorem exists_uniform_qFirst_comparison (B : ℝ) {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) :
    ∃ H F L : ℝ, 0 ≤ H ∧ 0 ≤ F ∧ 0 ≤ L ∧
      ∀ a b : QFirstInput, ‖a‖ ≤ B → d ≤ qFirstDet a → c ≤ |qFirstXX a| →
        ‖b-a‖ ≤ 1 → (4*max B 0+2)*‖b-a‖ ≤ d/2 → H*‖b-a‖ ≤ c/2 →
        (∀ x ∈ segment ℝ a b, c/2 ≤ |qFirstXX x|) ∧
        |qFirstDensityFactor b-qFirstDensityFactor a| ≤ F*‖b-a‖ ∧
        |qFirstLower b-qFirstLower a| ≤ L*‖b-a‖ := by
  obtain ⟨H,hH,hHb⟩ := qFirstXX_fderiv_bound (max B 0+1) (half_pos hd)
  obtain ⟨F,hF,hFb⟩ := qFirstTube_fderiv_bound qFirstDensityFactor
    qFirstDensityFactor_contDiffOn (max B 0+1) (half_pos hd) (half_pos hc)
  obtain ⟨L,hL,hLb⟩ := qFirstTube_fderiv_bound qFirstLower
    qFirstLower_contDiffOn (max B 0+1) (half_pos hd) (half_pos hc)
  refine ⟨H,F,L,hH,hF,hL,?_⟩
  intro a b ha hdet hxx hdist hsmall hxxsmall
  have hbase := qFirst_close_segment_subset_baseTube a b ha hdet hdist hsmall
  have hXXdiff : ∀ x ∈ segment ℝ a b, DifferentiableAt ℝ qFirstXX x := by
    intro x hx
    exact (qFirstXX_contDiffOn.contDiffAt (qFirstBase_isOpen.mem_nhds
      (qFirstBaseTube_subset_base (max B 0+1) (half_pos hd) (hbase hx)))).differentiableAt (by simp)
  have hfloor : ∀ x ∈ segment ℝ a b, c/2 ≤ |qFirstXX x| := by
    intro x hx
    have herr : |qFirstXX x-qFirstXX a| ≤ H*‖x-a‖ := by
      simpa only [Real.norm_eq_abs] using
        (convex_segment a b).norm_image_sub_le_of_norm_fderiv_le hXXdiff
          (fun y hy => hHb y (hbase hy)) (left_mem_segment ℝ a b) hx
    have hsmall' : |qFirstXX x-qFirstXX a| ≤ c/2 :=
      herr.trans ((mul_le_mul_of_nonneg_left (qFirst_segment_distance_le a b hx) hH).trans hxxsmall)
    have htriangle : |qFirstXX a| ≤ |qFirstXX x|+|qFirstXX x-qFirstXX a| := by
      calc
        _ = |qFirstXX x-(qFirstXX x-qFirstXX a)| := by congr 1; ring
        _ ≤ _ := abs_sub _ _
    linarith
  have htube : segment ℝ a b ⊆ qFirstTube (max B 0+1) (d/2) (c/2) :=
    fun x hx => ⟨hbase hx,hfloor x hx⟩
  have hcompare (f : QFirstInput → ℝ) (hf : ContDiffOn ℝ ∞ f qFirstDomain)
      (C : ℝ) (hCb : ∀ x ∈ qFirstTube (max B 0+1) (d/2) (c/2), ‖fderiv ℝ f x‖ ≤ C) :
      |f b-f a| ≤ C*‖b-a‖ := by
    have hdiff : ∀ x ∈ segment ℝ a b, DifferentiableAt ℝ f x := by
      intro x hx
      exact (hf.contDiffAt (qFirstDomain_isOpen.mem_nhds
        (qFirstTube_subset_domain (max B 0+1) (half_pos hd) (half_pos hc)
          (htube hx)))).differentiableAt (by simp)
    simpa only [Real.norm_eq_abs] using
      (convex_segment a b).norm_image_sub_le_of_norm_fderiv_le hdiff
        (fun x hx => hCb x (htube hx)) (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  exact ⟨hfloor,hcompare _ qFirstDensityFactor_contDiffOn F hFb,
    hcompare _ qFirstLower_contDiffOn L hLb⟩

end SmoothLocal.Pulse

end

end OAI
