import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.CleanupCost

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped NNReal ENNReal Topology
namespace SLEExactGauge
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator
open LoewnerRestart CenteredMoments BoxGrid

lemma allFrontiers_im_nonneg (a : ℝ) (b : GDriver) {z : ℂ}
    (hz : z∈allFrontiers a b) : 0≤z.im := by
  obtain ⟨T,hT⟩ := mem_iUnion.mp hz
  exact closure_minimal (fun w hw=>(alive_initial_im hw).le)
    (isClosed_le continuous_const Complex.continuous_im) (frontier_subset_closure hT)

lemma compact_subset_integer_box (K : Set ℂ) (hK : IsCompact K)
    (hH : ∀z∈K,0≤z.im) : ∃m : ℕ,K⊆box m := by
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_closedBall (0:ℂ)).mp hK.isBounded
  obtain ⟨m,hm⟩ := exists_nat_gt R
  refine ⟨m,fun z hz=>?_⟩
  have hn : ‖z‖≤(m:ℝ) := (by simpa only [mem_closedBall,dist_zero_right] using hR hz : ‖z‖≤R).trans hm.le
  have hx := abs_le.mp ((Complex.abs_re_le_norm z).trans hn)
  have hy := (le_abs_self z.im).trans ((Complex.abs_im_le_norm z).trans hn)
  exact ⟨hx,⟨hH z hz,hy⟩⟩

lemma capacity_dimension_eq (κ : ℝ) (_hκ : 0<κ) :
    dimension κ = 2-alpha (Target.a κ) := by
  unfold dimension alpha Target.a
  field_simp
  ring

namespace Target

 

theorem exactHausdorffGauge :
    ∀ κ : ℝ, 0 < κ → κ < 8 →
      ∃ h : ℝ → ℝ, IsHausdorffGauge h ∧
        ∀ W : WienerLaw, IsWiener W →
          ∀ᵐ b ∂W, ∀ s t : ℝ, 0 < s → s < t →
            0 < hausdorff h ((trace κ b) '' Icc s t) ∧
            hausdorff h ((trace κ b) '' Icc s t) < ∞ := by
  intro κ hκ hκ8
  refine ⟨parameterMomentGauge κ hκ hκ8,parameterMomentGauge_admissible κ hκ hκ8,?_⟩
  intro W hW
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  let : IsProbabilityMeasure (W.map driverHomeomorph) := inferInstance
  obtain ⟨M,hM⟩ := parameterMomentGauge_model κ hκ hκ8 W hW
  rw [hM,capacity_dimension_eq κ hκ]
  have hB := brownian_map_driver W hW
  have hl := driverMeasurableEquiv.measurableEmbedding.ae_map_iff.mp (M.hausdorff_positive hκ hB)
  have hu := driverMeasurableEquiv.measurableEmbedding.ae_map_iff.mp (M.frontier_boxes_finite hB)
  filter_upwards [hl,hu,trace_regular_actual_domains hκ hκ8 hW] with b hl hu hreg
  intro s t hs hst
  refine ⟨?_,?_⟩
  · simpa only [show driverMeasurableEquiv b=driverHomeomorph b from rfl,
      Homeomorph.symm_apply_apply] using hl s t hs hst
  · let K := trace κ b '' Icc s t
    have hK : IsCompact K := isCompact_Icc.image_of_continuousOn
      (hreg.1.mono (fun u hu=>hs.le.trans hu.1))
    have hKF : K⊆allFrontiers (a κ) (driverHomeomorph b) := by
      rintro z ⟨u,hu,rfl⟩
      exact mem_iUnion.mpr ⟨(κ*u).toNNReal,hreg.2.1 u (hs.le.trans hu.1)⟩
    obtain ⟨m,hm⟩ := compact_subset_integer_box K hK
      (fun z hz=>allFrontiers_im_nonneg _ _ (hKF hz))
    exact (hausdorff (M.gauge (2-alpha (a κ)))).mono
      (subset_inter hKF hm) |>.trans_lt (hu m)

end Target
end SLEExactGauge
end
end

end OAI
