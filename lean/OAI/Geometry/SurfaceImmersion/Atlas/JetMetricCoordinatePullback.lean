import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateTensorPullback
import OAI.Geometry.Immersion.ClosedSurface.TensorCoordinates

namespace OAI

/-! The complete metric-plus-polynomial operator transforms through fixed
nonlinear coordinates, including its finite periodic error. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial
open RealModes

lemma metric_coordinate_pullback {F : Base → Space} {T : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hT : ContDiff ℝ ∞ T) (x : Base) :
    realMetricTensor ((F ∘ T) ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) =
      tensorCoordinatePullbackValue T x
        (realMetricTensor (F ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry (T x))) := by
  let τ : SmallModes.Base → SmallModes.Base :=
    planeCoordinateIsometry ∘ T ∘ planeCoordinateIsometry.symm
  have hτ : ContDiff ℝ ∞ τ := planeCoordinateIsometry.contDiff.comp
    (hT.comp planeCoordinateIsometry.symm.contDiff)
  have he : (F ∘ planeCoordinateIsometry.symm) ∘ τ =
      (F ∘ T) ∘ planeCoordinateIsometry.symm := by
    funext p
    simp [τ]
  rw [← he,realMetricTensor_comp
    ((hF.comp planeCoordinateIsometry.symm.contDiff).differentiable (by simp) _) (hτ.differentiable (by simp) _)]
  have hd : fderiv ℝ τ (planeCoordinateIsometry x) = tensorCoordinateDerivative T x := by
    dsimp [τ]
    rw [fderiv_comp _ (planeCoordinateIsometry.differentiableAt)
      ((hT.comp planeCoordinateIsometry.symm.contDiff).differentiable (by simp) _),
      fderiv_comp _ (hT.differentiable (by simp) _) planeCoordinateIsometry.symm.differentiableAt]
    simp only [LinearIsometryEquiv.fderiv,LinearIsometryEquiv.symm_apply_apply]
    rfl
  simp only [PhaseMean.pullbackField,hd,τ,Function.comp_apply,LinearIsometryEquiv.symm_apply_apply,tensorCoordinatePullbackValue]

lemma metric_coordinate_pullback_germ {F H : Base → Space} {T : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hT : ContDiff ℝ ∞ T) {x : Base}
    (hrel : H =ᶠ[𝓝 x] F ∘ T) :
    realMetricTensor (H ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) =
      tensorCoordinatePullbackValue T x
        (realMetricTensor (F ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry (T x))) := by
  have hh : H ∘ planeCoordinateIsometry.symm =ᶠ[𝓝 (planeCoordinateIsometry x)]
      (F ∘ T) ∘ planeCoordinateIsometry.symm :=
    hrel.comp_tendsto (by simpa only [LinearIsometryEquiv.symm_apply_apply] using
      (planeCoordinateIsometry.symm.continuous.tendsto (planeCoordinateIsometry x)))
  rw [← metric_coordinate_pullback hF hT]
  ext i
  simp only [realMetricTensor_apply,realMetric,SmallModes.coordDeriv,hh.fderiv_eq]

namespace Perturbation
lemma coordinateMetricMap_coordinatePullback {n : ℕ} (P : Fin 3 → Fin n → Expression)
    {T S : Base → Base} (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {U : Set Base} (hU : IsOpen U)
    (hST : ∀ x ∈ U, S (T x) = x)
    (hTS : ∀ x ∈ U, T ∘ S =ᶠ[𝓝 (T x)] id)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hrel : ∀ x ∈ U, H x = G (T x)) (z : ℝ) {x : Base} (hx : x ∈ U) :
    coordinateMetricMap (tensorPolynomialCoordinatePullback P T S) z H (planeCoordinateIsometry x) =
      tensorCoordinatePullbackValue T x (coordinateMetricMap P z G (planeCoordinateIsometry (T x))) := by
  have hh : H =ᶠ[𝓝 x] G ∘ T := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hrel y hy
  simp only [coordinateMetricMap,Pi.add_apply,map_add]
  rw [metric_coordinate_pullback_germ hG hT hh,
    tensorPolynomialCoordinatePullback_eval P hT hS hU hST hTS hG hH hrel z 0 hx]

lemma coordinate_remainder_pullback {n : ℕ} (P : Fin 3 → Fin n → Expression)
    {T S : Base → Base} (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {U : Set Base} (hU : IsOpen U)
    (hST : ∀ x ∈ U, S (T x) = x)
    (hTS : ∀ x ∈ U, T ∘ S =ᶠ[𝓝 (T x)] id)
    {G H V W : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hV : ContDiff ℝ ∞ V)
    (hbase : ∀ x ∈ U, H x = G (T x)) (hvalue : ∀ x ∈ U, W x = V (T x))
    (B : Base → PhaseMean.Tensor) (z : ℝ) {x : Base} (hx : x ∈ U) :
    realMetricTensor (W ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) -
        coordinateMetricMap (tensorPolynomialCoordinatePullback P T S) z H (planeCoordinateIsometry x) -
        tensorCoordinatePullbackValue T x (B (T x)) =
      tensorCoordinatePullbackValue T x
        (realMetricTensor (V ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry (T x)) -
          coordinateMetricMap P z G (planeCoordinateIsometry (T x)) - B (T x)) := by
  have hv : W =ᶠ[𝓝 x] V ∘ T := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hvalue y hy
  rw [metric_coordinate_pullback_germ hV hT hv,
    coordinateMetricMap_coordinatePullback P hT hS hU hST hTS hG hH hbase z hx,map_sub,map_sub]

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
