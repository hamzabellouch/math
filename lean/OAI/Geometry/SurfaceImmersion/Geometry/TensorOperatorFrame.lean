import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPrimitiveOperator

namespace OAI

/-! Actual tensor operators and their inverses in a fixed primitive frame. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance operatorFrameFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance operatorFrameFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance operatorFrameDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance operatorFrameDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance operatorFrameSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance operatorFrameSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

def tensorOperatorFrame (i : B.centers) (p : M)
    (T : CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p) : TensorFiber →L[ℝ] TensorFiber :=
  ((B.tensorTriv i).continuousLinearMapAt ℝ p).comp (T.comp ((B.tensorTriv i).symmL ℝ p))

lemma tensorOperatorFrame_invertible_iff (i : B.centers) {p : M}
    (hp : p ∈ (chart (i : M)).source)
    (T : CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p) :
    (B.tensorOperatorFrame i p T).IsInvertible ↔ T.IsInvertible := by
  let e := (B.tensorTriv i).continuousLinearEquivAt ℝ p (B.tensorTriv_domain i hp)
  have he : B.tensorOperatorFrame i p T =
      (e : CovariantTwoTensor p →L[ℝ] TensorFiber).comp
        (T.comp (e.symm : TensorFiber →L[ℝ] CovariantTwoTensor p)) := by
    simp only [e,Trivialization.coe_continuousLinearEquivAt_eq',Trivialization.symm_continuousLinearEquivAt_eq']
    rfl
  rw [he,ContinuousLinearMap.isInvertible_equiv_comp,ContinuousLinearMap.isInvertible_comp_equiv]

lemma tensorOperatorFrame_inverse_apply (i : B.centers) {p : M}
    (hp : p ∈ (chart (i : M)).source)
    (T : CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p) (H : CovariantTwoTensor p) :
    (B.tensorOperatorFrame i p T).inverse ((B.tensorTriv i).continuousLinearMapAt ℝ p H) =
      (B.tensorTriv i).continuousLinearMapAt ℝ p (T.inverse H) := by
  let e := (B.tensorTriv i).continuousLinearEquivAt ℝ p (B.tensorTriv_domain i hp)
  have he : B.tensorOperatorFrame i p T =
      (e : CovariantTwoTensor p →L[ℝ] TensorFiber).comp
        (T.comp (e.symm : TensorFiber →L[ℝ] CovariantTwoTensor p)) := by
    simp only [e,Trivialization.coe_continuousLinearEquivAt_eq',Trivialization.symm_continuousLinearEquivAt_eq']
    rfl
  have hec : (e : CovariantTwoTensor p →L[ℝ] TensorFiber) =
      (B.tensorTriv i).continuousLinearMapAt ℝ p :=
    Trivialization.coe_continuousLinearEquivAt_eq' _ _
  rw [he, ← hec]
  change ((e : CovariantTwoTensor p →L[ℝ] TensorFiber).comp
    (T.comp (e.symm : TensorFiber →L[ℝ] CovariantTwoTensor p))).inverse (e H) = e (T.inverse H)
  simp only [ContinuousLinearMap.inverse_equiv_comp,ContinuousLinearMap.inverse_comp_equiv,
    ContinuousLinearEquiv.symm_symm,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

lemma primitiveCoefficient_inverse_in_frame
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (i : B.centers) {p : M} (hp : p ∈ (chart (i : M)).source)
    (T : CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p) (H : CovariantTwoTensor p) (j : Fin 3) :
    B.primitiveCoefficientField P (i,j) p (T.inverse H) =
      (P i (chart (i : M) p)).Q j (fiberToThree
        ((B.tensorOperatorFrame i p T).inverse ((B.tensorTriv i).continuousLinearMapAt ℝ p H))) := by
  rw [B.tensorOperatorFrame_inverse_apply i hp T H]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
