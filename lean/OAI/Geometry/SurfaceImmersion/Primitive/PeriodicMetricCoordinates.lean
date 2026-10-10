import OAI.Geometry.SurfaceImmersion.Atlas.SupportedAtlasMetric
import OAI.Geometry.SurfaceImmersion.Correction.SurfaceMeanTensor

namespace OAI

/-! Exact identification of the three coordinate metric entries of a
Euclidean periodic map in the primitive's product coordinates. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.LocalPeriodicExpansion
open JetPolynomial JetPolynomial.Perturbation SmallModes

lemma metric_coordinate_pair {f : JetPolynomial.Base → ClosedSurfaceR4.Space}
    (hf : ContDiff ℝ ∞ f) (p : JetPolynomial.Base) (b c : Bool) :
    RealModes.realMetric (spaceCoordinates ∘ f ∘ planeCoordinateIsometry.symm)
      (if b then dx else dy) (if c then dx else dy) (planeCoordinateIsometry p) =
      inner ℝ
        (fderiv ℝ f p (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
        (fderiv ℝ f p (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c)) := by
  have he := euclidean_metric_coordinate_value (f ∘ planeCoordinateIsometry.symm)
    ((hf.comp planeCoordinateIsometry.symm.contDiff).differentiable (by simp) (planeCoordinateIsometry p))
    (if b then dx else dy) (if c then dx else dy)
  rw [RealModes.evaluate_realMetricTensor] at he
  have hd (v : SmallModes.Base) :
      fderiv ℝ (f ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry p) v =
        fderiv ℝ f p (planeCoordinateIsometry.symm v) := by
    rw [fderiv_comp _ (hf.differentiable (by simp) _)
      planeCoordinateIsometry.symm.differentiableAt]
    simp only [ContinuousLinearMap.comp_apply,planeCoordinateIsometry.symm_apply_apply]
    change (fderiv ℝ f p)
      ((fderiv ℝ planeCoordinateIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap
        (planeCoordinateIsometry p)) v) = _
    rw [planeCoordinateIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap.fderiv]
    rfl
  have hdir (d : Bool) : planeCoordinateIsometry.symm (if d then dx else dy) =
      MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) d := by
    cases d <;> ext i <;> fin_cases i <;> rfl
  simpa only [Function.comp_assoc,hd,hdir] using he

lemma metric_coordinate_tensor {f : JetPolynomial.Base → ClosedSurfaceR4.Space}
    (hf : ContDiff ℝ ∞ f) (p : JetPolynomial.Base) :
    RealModes.realMetricTensor (spaceCoordinates ∘ f ∘ planeCoordinateIsometry.symm)
      (planeCoordinateIsometry p) =
    ![inner ℝ (fderiv ℝ f p (coordinateVector 0)) (fderiv ℝ f p (coordinateVector 0)),
      inner ℝ (fderiv ℝ f p (coordinateVector 0)) (fderiv ℝ f p (coordinateVector 1)),
      inner ℝ (fderiv ℝ f p (coordinateVector 1)) (fderiv ℝ f p (coordinateVector 1))] := by
  ext k
  fin_cases k
  · exact metric_coordinate_pair hf p true true
  · exact metric_coordinate_pair hf p true false
  · exact metric_coordinate_pair hf p false false

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
