import OAI.Geometry.SurfaceImmersion.Geometry.TensorOperatorFrame
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveOperatorConjugation
import OAI.Geometry.SurfaceImmersion.Correction.TensorSmoothingSymmetry

namespace OAI

/-! Coordinate conjugation of the actual primitive operator. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance frameAlgebraFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance frameAlgebraFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance frameAlgebraDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance frameAlgebraDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance frameAlgebraSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance frameAlgebraSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance frameAlgebraSectionGroup (p : M) : AddCommGroup (CovariantTwoTensor p) :=
  (frameAlgebraSectionNormed p).toAddCommGroup
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

lemma tensor_frame_symmetrizer (i : B.centers) {p : M} (hp : p ∈ (chart (i : M)).source)
    (H : TensorFiber) :
    (B.tensorTriv i).continuousLinearMapAt ℝ p (tensorSymmetrizer H) =
      tensorSymmetrizer ((B.tensorTriv i).continuousLinearMapAt ℝ p H) := by
  change B.bundleComponent B.tensorTriv i (fun _ => (show TensorFiber from tensorSymmetrizer H)) p =
    tensorSymmetrizer (B.bundleComponent B.tensorTriv i (fun _ => (show TensorFiber from H)) p)
  ext v w
  erw [B.tensorComponent_apply i _ hp,tensorSymmetrizer_apply,tensorSymmetrizer_apply,
    B.tensorComponent_apply i _ hp,B.tensorComponent_apply i _ hp]
  rfl

lemma tensor_inverse_frame_symmetrizer (i : B.centers) {p : M}
    (hp : p ∈ (chart (i : M)).source) (H : TensorFiber) :
    tensorSymmetrizer ((B.tensorTriv i).symmL ℝ p H) =
      (B.tensorTriv i).symmL ℝ p (tensorSymmetrizer H) := by
  have hd := B.tensorTriv_domain i hp
  have h := B.tensor_frame_symmetrizer i hp ((B.tensorTriv i).symmL ℝ p H)
  erw [(B.tensorTriv i).continuousLinearMapAt_symmL hd] at h
  have hh := congrArg ((B.tensorTriv i).symmL ℝ p) h
  erw [(B.tensorTriv i).symmL_continuousLinearMapAt hd] at hh
  exact hh

def covectorFrame (i : B.centers) (p : M) (v : Plane →L[ℝ] ℝ) : Plane →L[ℝ] ℝ :=
  v.comp ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p)

def coefficientFrame (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (i : B.centers) (a : B.centers × Fin 3) (p : M) : TensorFiber →L[ℝ] ℝ :=
  (B.primitiveCoefficientField P a p).comp ((B.tensorTriv i).symmL ℝ p)

lemma tensor_frame_square (i : B.centers) {p : M} (hp : p ∈ (chart (i : M)).source)
    (v : Plane →L[ℝ] ℝ) :
    (B.tensorTriv i).continuousLinearMapAt ℝ p (v.smulRight v) =
      (B.covectorFrame i p v).smulRight (B.covectorFrame i p v) := by
  ext x y
  have ht : p ∈ (trivializationAt Plane (TangentSpace planeModel) (i : M)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet,chart_source] using hp
  have h := B.tensorComponent_apply i (fun _ => v.smulRight v) hp x y
  change (B.tensorTriv i).continuousLinearMapAt ℝ p (v.smulRight v) x y = _ at h
  change (B.tensorTriv i).continuousLinearMapAt ℝ p (v.smulRight v) x y =
    v ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p x) *
      v ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p y)
  erw [(trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL_apply (R := ℝ) ht,
    (trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL_apply (R := ℝ) ht]
  exact h

lemma primitiveFullOperator_frame
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (i : B.centers) {p : M} (hp : p ∈ (chart (i : M)).source) :
    B.tensorOperatorFrame i p (B.primitiveFullOperator P psi phi p) =
      completedPrimitiveOperator (fun a => B.coefficientFrame P i a p)
        (fun a => psi a p) (fun a => B.covectorFrame i p (B.primitivePhaseCovector phi a p)) := by
  let e : TensorFiber →L[ℝ] TensorFiber := (B.tensorTriv i).continuousLinearMapAt ℝ p
  let f : TensorFiber →L[ℝ] TensorFiber := (B.tensorTriv i).symmL ℝ p
  have hef (H : TensorFiber) : e (f H) = H :=
    (B.tensorTriv i).continuousLinearMapAt_symmL (B.tensorTriv_domain i hp) H
  have hf (H : TensorFiber) : tensorSymmetrizer (f H) = f (tensorSymmetrizer H) :=
    B.tensor_inverse_frame_symmetrizer i hp H
  have hv (a : B.centers × Fin 3) :
      e ((B.primitivePhaseCovector phi a p).smulRight (B.primitivePhaseCovector phi a p)) =
        (B.covectorFrame i p (B.primitivePhaseCovector phi a p)).smulRight
          (B.covectorFrame i p (B.primitivePhaseCovector phi a p)) :=
    B.tensor_frame_square i hp _
  exact completedPrimitiveOperator_conjugate e f
    (fun a => B.primitiveCoefficientField P a p) (fun a => psi a p)
    (fun a => B.primitivePhaseCovector phi a p) _ hef hf hv

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
