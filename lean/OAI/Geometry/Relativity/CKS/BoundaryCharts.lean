import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.BoundaryFinite

namespace OAI

noncomputable section
open Set Manifold Bundle Filter
open scoped ContDiff Topology
namespace CKSBoundarySurface
section PlaneInsertion
attribute [local instance] two_atLeastTwo

lemma insertNormalZero_add (first second : E2) :
    insertNormalZero (first + second) = insertNormalZero first + insertNormalZero second := by
  ext index
  cases index using Fin.cases <;> simp [insertNormalZero]

lemma insertNormalZero_smul (scalar : ℝ) (point : E2) :
    insertNormalZero (scalar • point) = scalar • insertNormalZero point := by
  ext index
  cases index using Fin.cases <;> simp [insertNormalZero]

lemma insertNormalZero_continuous : Continuous insertNormalZero := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro index
  cases index using Fin.cases with
  | zero => exact continuous_const
  | succ index => exact PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) index

end PlaneInsertion

section PlaneProjection
attribute [local instance] two_atLeastTwo

lemma tangentialCoordinates_add (first second : E3) :
    tangentialCoordinates (first + second) =
      tangentialCoordinates first + tangentialCoordinates second := by
  ext index
  simp [tangentialCoordinates]

lemma tangentialCoordinates_smul (scalar : ℝ) (point : E3) :
    tangentialCoordinates (scalar • point) = scalar • tangentialCoordinates point := by
  ext index
  simp [tangentialCoordinates]

lemma tangentialCoordinates_continuous : Continuous tangentialCoordinates := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  exact continuous_pi fun index => PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) index.succ

end PlaneProjection

@[simp] lemma liftPlane_zero (z : E2) : liftPlane z 0 = 0 := rfl
@[simp] lemma liftPlane_succ (z : E2) (i : Fin 2) : liftPlane z i.succ = z i := rfl
@[simp] lemma dropPlane_apply (z : E3) (i : Fin 2) : dropPlane z i = z i.succ := rfl
@[simp] lemma drop_lift (z : E2) : dropPlane (liftPlane z) = z := by ext i; rfl
lemma lift_drop {z : E3} (hz : z 0 = 0) : liftPlane (dropPlane z) = z := by
  ext i
  cases i using Fin.cases with
  | zero => exact hz.symm
  | succ i => rfl

lemma liftHalf_continuous : Continuous liftHalf :=
  liftPlane.continuous.subtype_mk (fun _ => by simp)
@[simp] lemma I3_liftHalf (z : E2) : I3 (liftHalf z) = liftPlane z := rfl

attribute [local instance] halfSpaceDimension_neZero

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H3 M] [IsManifold I3 ∞ M]

lemma boundary_iff_zero (x y : M) (hy : y ∈ (chartAt H3 x).source) :
    y ∈ I3.boundary M ↔ (I3 (chartAt H3 x y)) 0 = 0 := by
  constructor
  · exact CKSIntrinsicGeometry.boundary_chart_zero x y (by simpa using hy)
  · intro hz
    apply (I3.isBoundaryPoint_iff_not_isInteriorPoint y).mpr
    intro hi
    have hin := (I3.isInteriorPoint_iff_of_mem_atlas
      (by simp : (∞ : ℕ∞ω) ≠ 0) (chart_mem_atlas H3 x) hy).mp hi
    have hr := (chartAt H3 x).interior_extend_target_subset_interior_range hin
    have hp : 0 < (I3 (chartAt H3 x y)) 0 := by
      simpa only [I3, interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq,
        OpenPartialHomeomorph.extend_coe, Function.comp_apply] using hr
    rw [hz] at hp
    exact (lt_irrefl 0) hp

lemma chart_inverse_boundary (x : M) {z : E2}
    (hz : liftHalf z ∈ (chartAt H3 x).target) :
    (chartAt H3 x).symm (liftHalf z) ∈ I3.boundary M := by
  apply (boundary_iff_zero x _ ((chartAt H3 x).map_target hz)).mpr
  rw [(chartAt H3 x).right_inv hz]
  rfl

end CKSBoundarySurface

end

end OAI
