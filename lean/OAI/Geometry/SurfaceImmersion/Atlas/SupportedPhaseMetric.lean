import OAI.Geometry.SurfaceImmersion.Geometry.LocalizedMetricDefect
import OAI.Geometry.SurfaceImmersion.Atlas.SupportedChartPullback

namespace OAI

/-! The actual supported phase-chart map realizes the localized metric
identity. Its cutoff is fixed before the fast scale is chosen. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

theorem supported_phase_metric_defect {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e)
    (hi : ContDiff ℝ ∞ e.symm) {χ : Base → ℝ}
    (hχ : tsupport χ ⊆ e.source) {K : Set Base} (hK : IsCompact K)
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    {H V : Base → JetPolynomial.Space} (hH : ContDiff ℝ ∞ H) (hV : ContDiff ℝ ∞ V)
    (hs : tsupport (V-H ∘ e.symm) ⊆ K)
    (B : Base → PhaseMean.Tensor) (z : ℝ) (x : Base) :
    let W := H + supportedChartPullback e χ (V-H ∘ e.symm)
    RealModes.realMetricTensor (W ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) -
        RealModes.realMetricTensor (H ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) -
        coordinatePolynomialValue
          (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback P e e.symm))
          z H 0 (planeCoordinateIsometry x) - localizedTensorPullback e χ B x =
      localizedTensorPullback e χ
        (fun y => RealModes.realMetricTensor (V ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry y) -
          coordinateMetricMap P z (H ∘ e.symm) (planeCoordinateIsometry y) - B y) x := by
  let f := supportedChartPullback e χ (V-H ∘ e.symm)
  have hsf : tsupport f ⊆ e.symm '' K := supportedChartPullback_support e hi hK hχ hs
  have hsub : (H+f)-H = f := by funext y; simp
  apply localized_metric_defect P e he hi hχ (hH.comp hi) hH hV
  · intro y hy
    simp only [Function.comp_apply,e.left_inv hy]
  · intro y hy
    have hh := supportedChartPullback_eq e hs hone hy
    change H y + supportedChartPullback e χ (V-H ∘ e.symm) y = V (e y)
    rw [hh]
    simp only [Pi.sub_apply,Function.comp_apply,e.left_inv hy]
    abel
  · intro y hy
    rw [hsub] at hy
    exact hone y (hsf hy)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
