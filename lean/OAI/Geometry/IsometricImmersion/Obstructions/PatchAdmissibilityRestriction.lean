import OAI.Geometry.IsometricImmersion.Metrics.PatchTensorRestriction

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

theorem PatchAdmissibleHeight.congr_metric_on_open
    {g h : MetricField} {z : Coord → ℝ} (hadm : PatchAdmissibleHeight g z)
    {W : Set Coord} (hW : IsOpen W) (hSW : modelSquare ⊆ W) (heq : EqOn g h W) :
    PatchAdmissibleHeight h z := by
  obtain ⟨U,hU,hSU,hg,hz,hD,hE,hyy,hq⟩ := hadm
  have hevent (p : Coord) (hp : p ∈ modelSquare) : g =ᶠ[𝓝 p] h := by
    filter_upwards [hW.mem_nhds (hSW hp)] with q hq
    exact heq hq
  have hmetric : SmoothPositiveOn h (U ∩ W) := by
    constructor
    · intro i j
      apply ((hg.1 i j).mono inter_subset_left).congr
      intro p hp
      exact congrFun (congrFun (heq hp.2).symm i) j
    · intro p hp
      rw [← heq hp.2]
      exact hg.2 p hp.1
  refine ⟨U ∩ W,hU.inter hW,(fun p hp => ⟨hSU hp,hSW hp⟩),hmetric,
    hz.mono inter_subset_left,?_,?_,?_,?_⟩
  · intro p hp
    rw [← covHessian_eq_of_metric_eventuallyEq (hevent p hp) z,
      ← gaussianCurvature_eq_of_eventuallyEq (hevent p hp),
      ← heightEnergy_eq_of_metric_eventuallyEq (hevent p hp) z]
    exact hD p hp
  · intro p hp
    rw [← heightEnergy_eq_of_metric_eventuallyEq (hevent p hp) z]
    exact hE p hp
  · intro p hp
    rw [← covHessian_eq_of_metric_eventuallyEq (hevent p hp) z]
    exact hyy p hp
  · intro p hp
    unfold hessianQuotient
    rw [← covHessian_eq_of_metric_eventuallyEq (hevent p hp) z]
    exact hq p hp

theorem assembledPatchMetric_admissible_local
    (g : MetricField) (eta : PatchAddress → SymmetricPerturbation) (a : PatchAddress)
    {z : Coord → ℝ}
    (hadm : PatchAdmissibleHeight
      (affinePullbackMetric (assembledPatchMetric g eta) (patchAddressCenter a) (patchAddressMatrix a)) z) :
    PatchAdmissibleHeight (localPatchMetric g eta a) z := by
  apply hadm.congr_metric_on_open Metric.isOpen_ball (W := Metric.ball (0 : Coord) 4)
  · intro p hp
    have hnorm : ‖p‖ ≤ 3 := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)).mpr
      intro i
      simpa only [Real.norm_eq_abs] using (abs_le.mpr ⟨hp.1 i,hp.2 i⟩)
    simpa only [Metric.mem_ball,dist_zero_right] using (lt_of_le_of_lt hnorm (by norm_num : (3 : ℝ) < 4))
  · intro p hp
    apply assembledPatchMetric_pullback_eq_on_closedPatchBox g eta a
    apply (mem_closedPatchBox_iff_norm_le p).mpr
    exact (by simpa only [Metric.mem_ball,dist_zero_right] using hp : ‖p‖ < 4).le

end SmoothLocal.Geometry

end

end OAI
