import OAI.Geometry.SurfaceImmersion.Primitive.SurfacePrimitiveError
import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateTaylorIdentity

namespace OAI

/-! The primitive's three mean metric coefficients are exactly the tensor
operator used by the finite parametrix, in its product coordinates. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion
open CovarianceCorrector

variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

def meanTensorPolynomial (n : ℕ) : Fin 3 → Fin n → Expression :=
  ![l.meanPolynomial n true true,l.meanPolynomial n true false,l.meanPolynomial n false false]

def meanTensorOperator (n : ℕ) (z : ℝ) (G : JetPolynomial.Base → JetPolynomial.Space) :
    SmallModes.Base → PhaseMean.Tensor := fun p =>
  ![l.meanOperator n true true z G (planeCoordinateIsometry.symm p),
    l.meanOperator n true false z G (planeCoordinateIsometry.symm p),
    l.meanOperator n false false z G (planeCoordinateIsometry.symm p)]

lemma meanTensorPolynomial_smooth (n : ℕ) (k : Fin 3) (r : Fin n) :
    (l.meanTensorPolynomial n k r).SmoothCoeffs O := by
  fin_cases k <;> exact l.meanPolynomial_smooth n _ _ r

lemma meanTensorPolynomial_order (n : ℕ) (k : Fin 3) (r : Fin n) :
    (l.meanTensorPolynomial n k r).order ≤ 2*(n+1)+1 := by
  fin_cases k <;> exact l.meanPolynomial_order n _ _ r

private lemma realMetric_coordinate {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (p : SmallModes.Base) (b c : Bool) :
    RealModes.realMetric (G ∘ planeCoordinateIsometry.symm)
        (if b then SmallModes.dx else SmallModes.dy)
        (if c then SmallModes.dx else SmallModes.dy) p =
      inner ℝ
        (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q))
          (planeCoordinateIsometry.symm p)
          (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
        (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q))
          (planeCoordinateIsometry.symm p)
          (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c)) := by
  have hcomp (v : SmallModes.Base) :
      fderiv ℝ (G ∘ planeCoordinateIsometry.symm) p v =
        fderiv ℝ G (planeCoordinateIsometry.symm p) (planeCoordinateIsometry.symm v) := by
    rw [fderiv_comp p (hG.differentiable (by simp) _) planeCoordinateIsometry.symm.differentiableAt]
    change (fderiv ℝ G (planeCoordinateIsometry.symm p))
      ((fderiv ℝ planeCoordinateIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap p) v) = _
    rw [planeCoordinateIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap.fderiv]
    rfl
  have heuc (v : JetPolynomial.Base) :
      fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q))
        (planeCoordinateIsometry.symm p) v =
      JetVelocityCoordinates.toEuclidean (fderiv ℝ G (planeCoordinateIsometry.symm p) v) := by
    change (fderiv ℝ ((JetVelocityCoordinates.toEuclidean : JetPolynomial.Space → Euclidean) ∘ G)
      (planeCoordinateIsometry.symm p)) v = _
    rw [fderiv_comp (planeCoordinateIsometry.symm p)
      JetVelocityCoordinates.toEuclidean.differentiableAt (hG.differentiable (by simp) _)]
    change (fderiv ℝ JetVelocityCoordinates.toEuclidean.toContinuousLinearMap
      (G (planeCoordinateIsometry.symm p))) ((fderiv ℝ G (planeCoordinateIsometry.symm p)) v) = _
    rw [JetVelocityCoordinates.toEuclidean.toContinuousLinearMap.fderiv]
    rfl
  have hdir (d : Bool) :
      planeCoordinateIsometry.symm (if d then SmallModes.dx else SmallModes.dy) =
        MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) d := by
    cases d <;> ext i <;> fin_cases i <;> rfl
  change (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) p
    (if b then SmallModes.dx else SmallModes.dy)) ⬝ᵥ
    (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) p
      (if c then SmallModes.dx else SmallModes.dy)) = _
  rw [hcomp,hcomp,heuc,heuc,inner_toEuclidean,hdir,hdir]

/-- No identification of metric operators is assumed: the coordinate
conversion and all three polynomial coefficients are proved equal. -/
theorem coordinateMetricMap_eq_meanTensorOperator
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (n : ℕ) (z : ℝ) :
    Perturbation.coordinateMetricMap (l.meanTensorPolynomial n) z G =
      l.meanTensorOperator n z G := by
  funext p k
  fin_cases k
  all_goals
    dsimp only [Perturbation.coordinateMetricMap,RealModes.realMetricTensor,
      Perturbation.coordinatePolynomialValue,meanTensorOperator,meanTensorPolynomial,
      meanOperator,Perturbation.eval,Pi.add_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two]
  · change RealModes.realMetric (G ∘ planeCoordinateIsometry.symm)
      SmallModes.dx SmallModes.dx p + _ = _
    have hh := realMetric_coordinate hG p true true
    simp only [↓reduceIte] at hh
    rw [hh]
    rfl
  · change RealModes.realMetric (G ∘ planeCoordinateIsometry.symm)
      SmallModes.dx SmallModes.dy p + _ = _
    have hh := realMetric_coordinate hG p true false
    simp only [Bool.false_eq_true, ↓reduceIte] at hh
    rw [hh]
    rfl
  · change RealModes.realMetric (G ∘ planeCoordinateIsometry.symm)
      SmallModes.dy SmallModes.dy p + _ = _
    have hh := realMetric_coordinate hG p false false
    simp only [Bool.false_eq_true, ↓reduceIte] at hh
    rw [hh]
    rfl

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
