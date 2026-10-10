import OAI.Geometry.SurfaceImmersion.Primitive.ReferenceCircularMargins
import OAI.Geometry.SurfaceImmersion.Geometry.TensorOperatorFrame
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteScalarBounds

namespace OAI

/-! Compact chart margins imply invertibility of the actual global tensor
operator and positivity of every active primitive coefficient. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance refOperatorFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance refOperatorFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance refOperatorDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance refOperatorDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance refOperatorSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance refOperatorSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

 theorem operator_stability : ∃ eps : ℝ, 0 < eps ∧
    ∀ (T : ∀ p : M, CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p)
      (u : ∀ p : M, CovariantTwoTensor p),
    (∀ i p, p ∈ tsupport (d.B.weight i) →
      ‖d.B.tensorOperatorFrame i p (T p)-ContinuousLinearMap.id ℝ TensorFiber‖ < eps) →
    (∀ i p, p ∈ tsupport (d.B.weight i) →
      ‖(d.B.tensorTriv i).continuousLinearMapAt ℝ p (u p)-
        d.chartReference i (chart (i : M) p)‖ < eps) →
    (∀ p, (T p).IsInvertible) ∧
      ∀ (a : d.B.centers × Fin 3) p, p ∈ tsupport (d.B.weight a.1) →
        0 < d.B.primitiveCoefficientField d.basis a p ((T p).inverse (u p)) := by
  choose e he hmargin using fun a : d.B.centers × Fin 3 => d.inverse_margin a.1 a.2
  obtain ⟨eps,heps,hle⟩ := finite_positive_lower he
  refine ⟨eps,heps,?_⟩
  intro T u hT hu
  have hlocal (a : d.B.centers × Fin 3) (p : M) (hp : p ∈ tsupport (d.B.weight a.1)) :=
    hmargin a (chart (a.1 : M) p) ⟨p,hp,rfl⟩ (d.B.tensorOperatorFrame a.1 p (T p))
      ((d.B.tensorTriv a.1).continuousLinearMapAt ℝ p (u p))
      ((hT a.1 p hp).trans_le (hle a)) ((hu a.1 p hp).trans_le (hle a))
  constructor
  · intro p
    obtain ⟨i,hi⟩ := d.B.exists_weight_ne_zero p
    have hp := subset_tsupport _ hi
    exact (d.B.tensorOperatorFrame_invertible_iff i (d.B.weight_support i hp) (T p)).mp
      (hlocal (i,0) p hp).1
  · intro a p hp
    rw [d.B.primitiveCoefficient_inverse_in_frame d.basis a.1 (d.B.weight_support a.1 hp) (T p) (u p) a.2]
    exact (hlocal a p hp).2

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
