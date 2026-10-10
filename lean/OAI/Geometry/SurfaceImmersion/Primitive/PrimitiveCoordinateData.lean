import OAI.Geometry.SurfaceImmersion.Atlas.PhaseCovectorFamily
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveAmplitudeParameterBounds
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveOperatorMask

namespace OAI

/-! Fixed active-chart coordinate data represent the genuine inverse and
amplitude, while vanishing cutoff terms eliminate the other charts. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance coordinateDataFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance coordinateDataFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance coordinateDataDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance coordinateDataDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance coordinateDataSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance coordinateDataSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

def primitiveCoordinateData
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (u : ∀ p : M, CovariantTwoTensor p) (i : B.centers)
    (S : Set (B.centers × Fin 3)) (y : JetPolynomial.Base) :
    PrimitiveAmplitudeData (B.centers × Fin 3) := by
  classical
  exact (((fun a => if a ∈ S then B.coefficientFrameRead P i a y else 0,
    fun a => psi a ((chart (i : M)).symm y)),
    fun a => if a ∈ S then B.phaseCovectorRead i (phi a) y else 0),
    (B.tensorTriv i).continuousLinearMapAt ℝ ((chart (i : M)).symm y)
      (u ((chart (i : M)).symm y)))

omit [CompactSpace M] in
lemma primitiveCoordinateData_operator
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (u : ∀ p : M, CovariantTwoTensor p) (i : B.centers)
    (S : Set (B.centers × Fin 3)) {p : M} (hp : p ∈ (chart (i : M)).source)
    (hz : ∀ a ∉ S, psi a p = 0) :
    primitiveDataOperator (B.primitiveCoordinateData P psi phi u i S (chart (i : M) p)).1 =
      B.tensorOperatorFrame i p (B.primitiveFullOperator P psi phi p) := by
  classical
  rw [B.primitiveFullOperator_frame P psi phi i hp,
    completedPrimitiveOperator_mask _ _ _ (fun _ => 0) S hz]
  unfold primitiveCoordinateData primitiveDataOperator
  rw [(chart (i : M)).left_inv hp]
  simp only [coefficientFrameRead,(chart (i : M)).left_inv hp]
  congr 1
  funext a
  split_ifs with ha
  · exact (B.covectorFrame_mfderiv (phi a) (hphi a) i hp).symm
  · rfl

omit [CompactSpace M] in
lemma coefficientFrame_inverse
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (i : B.centers) (a : B.centers × Fin 3) {p : M}
    (hp : p ∈ (chart (i : M)).source)
    (T : CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p) (H : CovariantTwoTensor p) :
    B.coefficientFrame P i a p
      ((B.tensorOperatorFrame i p T).inverse ((B.tensorTriv i).continuousLinearMapAt ℝ p H)) =
      B.primitiveCoefficientField P a p (T.inverse H) := by
  rw [B.tensorOperatorFrame_inverse_apply i hp T H]
  change B.primitiveCoefficientField P a p
    ((B.tensorTriv i).symmL ℝ p ((B.tensorTriv i).continuousLinearMapAt ℝ p (T.inverse H))) = _
  erw [(B.tensorTriv i).symmL_continuousLinearMapAt (B.tensorTriv_domain i hp)]

omit [CompactSpace M] in
lemma primitiveCoordinateData_amplitude
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (u : ∀ p : M, CovariantTwoTensor p) (i : B.centers)
    (S : Set (B.centers × Fin 3)) (a : B.centers × Fin 3) (ha : a ∈ S)
    {p : M} (hp : p ∈ (chart (i : M)).source) (hz : ∀ b ∉ S, psi b p = 0) :
    primitiveParameterAmplitude a (B.primitiveCoordinateData P psi phi u i S (chart (i : M) p)) =
      B.correctedPrimitiveAmplitude P psi phi u a p := by
  classical
  unfold primitiveParameterAmplitude primitiveParameterCoefficient primitiveParameterInverse
  rw [B.primitiveCoordinateData_operator P psi phi hphi u i S hp hz]
  change psi a ((chart (i : M)).symm (chart (i : M) p)) *
    Real.sqrt ((if a ∈ S then B.coefficientFrameRead P i a (chart (i : M) p) else 0)
      ((B.tensorOperatorFrame i p (B.primitiveFullOperator P psi phi p)).inverse
        ((B.tensorTriv i).continuousLinearMapAt ℝ ((chart (i : M)).symm (chart (i : M) p))
          (u ((chart (i : M)).symm (chart (i : M) p)))))) = _
  rw [ite_eq_left ha,(chart (i : M)).left_inv hp]
  unfold coefficientFrameRead
  rw [(chart (i : M)).left_inv hp,B.coefficientFrame_inverse P i a hp]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
