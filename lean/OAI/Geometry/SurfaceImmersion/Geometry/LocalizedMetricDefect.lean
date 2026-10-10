import OAI.Geometry.SurfaceImmersion.Atlas.JetMetricCoordinatePullback
import OAI.Geometry.SurfaceImmersion.Correction.CutoffTensorPolynomial
import OAI.Geometry.SurfaceImmersion.Geometry.LocalizedTensorPullbackBound

namespace OAI

/-! Exact localized metric defect in a nonlinear chart. The cutoff is
one on the actual map increment, so no boundary metric term is discarded. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial
open RealModes

lemma coordinateMetric_eq_of_sub_notMem_tsupport {H W : Base → Space} {x : Base}
    (hx : x ∉ tsupport (W-H)) :
    realMetricTensor (W ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) =
      realMetricTensor (H ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) := by
  have he : W =ᶠ[𝓝 x] H := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    exact sub_eq_zero.mp hy
  have hh : W ∘ planeCoordinateIsometry.symm =ᶠ[𝓝 (planeCoordinateIsometry x)]
      H ∘ planeCoordinateIsometry.symm :=
    he.comp_tendsto (by simpa only [LinearIsometryEquiv.symm_apply_apply] using
      (planeCoordinateIsometry.symm.continuous.tendsto (planeCoordinateIsometry x)))
  ext k
  simp only [realMetricTensor_apply,realMetric,SmallModes.coordDeriv,hh.fderiv_eq]

namespace Perturbation

theorem localized_metric_defect {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e)
    (hi : ContDiff ℝ ∞ e.symm) {χ : Base → ℝ}
    (hχ : tsupport χ ⊆ e.source)
    {G H V W : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hV : ContDiff ℝ ∞ V)
    (hbase : ∀ x ∈ e.source, H x = G (e x))
    (hvalue : ∀ x ∈ e.source, W x = V (e x))
    (hone : ∀ x ∈ tsupport (W-H), χ x = 1)
    (B : Base → PhaseMean.Tensor) (z : ℝ) (x : Base) :
    realMetricTensor (W ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) -
        realMetricTensor (H ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) -
        coordinatePolynomialValue
          (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback P e e.symm))
          z H 0 (planeCoordinateIsometry x) - localizedTensorPullback e χ B x =
      localizedTensorPullback e χ
        (fun y => realMetricTensor (V ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry y) -
          coordinateMetricMap P z G (planeCoordinateIsometry y) - B y) x := by
  rw [cutoffTensorPolynomial_eval]
  have hfix : χ x •
      (realMetricTensor (W ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) -
       realMetricTensor (H ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x)) =
      realMetricTensor (W ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) -
       realMetricTensor (H ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) := by
    by_cases hx : x ∈ tsupport (W-H)
    · rw [hone x hx,one_smul]
    · rw [coordinateMetric_eq_of_sub_notMem_tsupport hx,sub_self,smul_zero]
  by_cases hzero : χ x = 0
  · rw [hzero,zero_smul] at hfix
    simp only [localizedTensorPullback,hzero,zero_smul,sub_zero]
    exact hfix.symm
  have hx : x ∈ e.source := hχ (subset_tsupport χ hzero)
  have hTS : ∀ y ∈ e.source, e ∘ e.symm =ᶠ[𝓝 (e y)] id := by
    intro y hy
    filter_upwards [e.open_target.mem_nhds (e.map_source hy)] with q hq
    exact e.right_inv hq
  have hr := coordinate_remainder_pullback P he hi e.open_source
    (fun _ hx => e.left_inv hx) hTS hG hH hV hbase hvalue B z hx
  have hp := congrArg (fun a : PhaseMean.Tensor => χ x • a) hr
  simp only [coordinateMetricMap,Pi.add_apply,smul_sub,smul_add] at hp
  dsimp only [localizedTensorPullback]
  rw [← hfix]
  simpa only [smul_sub,sub_add_eq_sub_sub,coordinateMetricMap,Pi.add_apply] using hp

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
