import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveCoordinateData

namespace OAI

/-! Entrywise perturbations bound the actual finite coordinate data. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance coordToleranceFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance coordToleranceFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance coordToleranceDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance coordToleranceDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance coordToleranceSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance coordToleranceSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

lemma primitiveCoordinateData_sub_lt
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi psi0 phi phi0 : (B.centers × Fin 3) → M → ℝ)
    (u u0 : ∀ p : M, CovariantTwoTensor p) (i : B.centers)
    (S : Set (B.centers × Fin 3)) {p : M} (hp : p ∈ (chart (i : M)).source)
    {eps : ℝ} (heps : 0 < eps)
    (hw : ∀ a, |psi a p-psi0 a p| < eps)
    (hv : ∀ a ∈ S, ‖B.phaseCovectorRead i (phi a) (chart (i : M) p)-
      B.phaseCovectorRead i (phi0 a) (chart (i : M) p)‖ < eps)
    (hH : ‖(B.tensorTriv i).continuousLinearMapAt ℝ p (u p)-
      (B.tensorTriv i).continuousLinearMapAt ℝ p (u0 p)‖ < eps) :
    ‖B.primitiveCoordinateData P psi phi u i S (chart (i : M) p)-
      B.primitiveCoordinateData P psi0 phi0 u0 i S (chart (i : M) p)‖ < eps := by
  classical
  let q := fun a => if a ∈ S then B.coefficientFrameRead P i a (chart (i : M) p) else 0
  let v := fun a => if a ∈ S then B.phaseCovectorRead i (phi a) (chart (i : M) p) else 0
  let v0 := fun a => if a ∈ S then B.phaseCovectorRead i (phi0 a) (chart (i : M) p) else 0
  unfold primitiveCoordinateData
  rw [(chart (i : M)).left_inv hp]
  change max (max (max ‖q-q‖ ‖(fun a => psi a p)-(fun a => psi0 a p)‖) ‖v-v0‖)
    ‖(B.tensorTriv i).continuousLinearMapAt ℝ p (u p)-
      (B.tensorTriv i).continuousLinearMapAt ℝ p (u0 p)‖ < eps
  rw [sub_self,norm_zero]
  refine max_lt (max_lt (max_lt heps ?_) ?_) hH
  · apply (pi_norm_lt_iff heps).mpr
    intro a
    simpa only [Pi.sub_apply,Real.norm_eq_abs] using hw a
  · apply (pi_norm_lt_iff heps).mpr
    intro a
    dsimp only [v,v0,Pi.sub_apply]
    split_ifs with ha
    · exact hv a ha
    · simpa only [sub_self,norm_zero] using heps

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
